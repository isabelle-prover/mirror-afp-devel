(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature PROGRAM_ANALYSIS =
sig
  type 'a wrap = 'a RegionExtras.wrap
  type 'ce ctype = 'ce Absyn.ctype
  type expr = Absyn.expr
  type ecenv = Absyn.ecenv
  type s2s_config = {anon_vars : bool, owners : string list,
                     allow_underscore_idents : bool,
                     munge_info_fname : Path.T option, prog_name: string}

  type 'a rcd_env = (string * (CType.rcd_kind * (string wrap * 'a) list * Region.t * CType.attribute list)) list
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

  type selector = Expr.selector
  type fun_ptr_call_info = (int ctype * int ctype list) *
                           (string * AstDatatype.var_info * selector list) list * (* potentially called functions, or if selectors not null an object-method *)
                           bool (* true if C-style object method *)

  datatype fncall_type = DirectCall of string
                       | FnPtrCall of fun_ptr_call_info

  val is_function:  (string * AstDatatype.var_info * selector list) -> bool

  val fncall_ord : fncall_type * fncall_type -> order


  type callgraph =
    {callees: string Binaryset.set Symtab.table, callers: string Binaryset.set Symtab.table}

  val closure: string Binaryset.set Symtab.table -> string list -> Symtab.key Binaryset.set

  datatype clang_record_name = Named of string | Anonymous of SourcePos.t
  datatype clang_field_kind = 
    Strct of {record_name: clang_record_name, field_name: string option} | 
    Un of {record_name: clang_record_name, field_name: string option} | 
    Fld of {name:string, typ:string}
  type clang_field = {kind: clang_field_kind, level: int}
  type clang_field_info = {field: clang_field, offset: int}
  type clang_record_info = {
    header: clang_field_info,
    flds: clang_field_info list,
    size: int,
    align: int}

  type csenv
  type embedded_fncall_exprs = (expr * fncall_type list) list Symtab.table
  val cse2ecenv : Proof.context -> csenv -> ecenv
  val get_array_mentions : csenv -> (int ctype * int) Binaryset.set
  val get_prog_name: csenv -> string
  val get_senv : csenv -> senv
  val get_pruned_senv : csenv -> senv
  val get_union_variants : csenv -> union_variants
  val variant_origin: csenv -> string -> string option
  val get_clang_record_infos: csenv -> clang_record_info list
  val map_clang_record_infos: (clang_record_info list -> clang_record_info list) -> csenv -> csenv 
  val get_rettype : string -> csenv -> int ctype option
  val get_heaptypes : csenv -> int ctype Binaryset.set
  val get_usedtypes : csenv -> int ctype Binaryset.set
  val compute_callgraphs : csenv -> callgraph
  val compute_callgraphs_with_exit : csenv -> callgraph
  val get_addressed : csenv -> (expr * selector list) list XMSymTab.table
  val is_addressed  : csenv -> (MString.t * string option) -> bool
  val get_addressed_types: csenv -> selector list Ord_List.T Absyn.CTypeTab.table
  val get_callgraph : csenv -> fncall_type Binaryset.set Symtab.table
  val get_direct_callees: csenv -> Symtab.key -> string list
  val get_fun_ptr_callees: csenv -> Symtab.key -> string list
  val get_fun_ptr_calls: csenv -> string -> fun_ptr_call_info list
  val has_fun_ptr_calls: csenv -> string -> bool
  val program_has_fun_ptr_calls: csenv -> bool
  val functions_with_local_fun_ptr_calls: csenv -> string list
  val get_fun_ptr_params: csenv -> ((string * AstDatatype.var_info * selector list) list) option list Symtab.table
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
  val get_fnspecs: csenv -> AstDatatype.fnspec list Symtab.table
  val get_fun_ty: csenv -> string -> int CTypeDatatype.ctype option
  val get_embedded_fncalls : csenv -> fncall_type Binaryset.set
  val get_embedded_fncall_exprs: csenv -> embedded_fncall_exprs
  val get_referenced_funs: csenv -> string list Symtab.table
  val get_all_referenced_funs: {with_proto: bool} -> csenv -> Symtab.key list
  val get_referenced_funs_global: csenv -> string list
  val get_referenced_funs_via_const_globals: csenv -> Symtab.key -> string list
  val get_functions_used_as_fun_ptr_params: csenv -> string list
  val has_fun_ptr_params_called_with_object_method: csenv -> bool
  val functions_with_fun_ptr_calls: csenv -> string list
  val get_functions_used_via_fun_ptr: csenv -> string list
  val get_functions_with_sig: csenv -> (int ctype * int ctype list) -> string list
  val get_addressed_vis : string option -> csenv -> var_info list
  val get_addressed_globals : csenv -> string -> string list
  val get_local_info: csenv -> MString.t * string option -> {kind:NameGeneration.var_kind, addressed:bool,info:var_info} option
  val has_addressable_variables: csenv -> string -> bool
  val callers_with_addressable_variables: csenv -> string -> string list
  val get_global_addressed : csenv -> (MString.t * (Absyn.expr * selector list) list) list
  val get_vi_nm_info : csenv -> var_info -> nm_info
  val get_fun_modifies : csenv -> string -> modify_var Binaryset.set option
  val get_functions : csenv -> string list
  val get_max_function_arity : csenv -> int
  val get_non_proto_functions : csenv -> string list
  val has_body_spec : csenv -> Symtab.key -> bool
  val get_non_proto_and_body_spec_functions : csenv -> string list
  val get_fninfo : csenv -> (int ctype * bool * var_info list) Symtab.table
  val get_hpfninfo : csenv -> Absyn.ext_decl Symtab.table
  val get_constant_global_fun_ptrs : csenv -> (string * string list) list
  val map_constant_global_fun_ptrs : ((string * string list) list ->  (string * string list) list)
         -> csenv -> csenv
  val get_global_fun_ptrs_grouped_by_type: csenv -> (string * int CTypeDatatype.ctype) list list
  val get_global_fun_ptr_group_with_same_type: csenv -> string -> string list
  val get_cliques : csenv -> string list list
  val map_cliques : (string list list -> string list list ) -> csenv -> csenv
  val get_final_callgraph : csenv -> callgraph
  val get_final_callers : csenv -> string list -> string list
  val get_final_callees : csenv -> string list -> string list
  val map_final_callgraph: (callgraph -> callgraph) -> csenv -> csenv
  val get_final_callgraph_with_exit : csenv -> callgraph
  val map_final_callgraph_with_exit: (callgraph -> callgraph) -> csenv -> csenv
  val get_clique : csenv -> string -> string list option
  val get_fun_ptr_core_clique : csenv -> string list
  val map_fun_ptr_core_clique: (string list -> string list) -> csenv -> csenv
  val get_fun_ptr_clique : csenv -> string list
  val get_fun_ptr_clique_fun_ptrs : csenv -> string list
  val get_fun_ptr_parameters: csenv -> Symtab.key -> var_info option list
  val has_fun_ptr_parameters: csenv -> Symtab.key -> bool
  val all_fun_ptr_parameters: csenv -> var_info list
  val all_fun_ptr_parameter_types: csenv -> int CTypeDatatype.ctype list
  val all_method_fun_ptr_types: csenv -> int CTypeDatatype.ctype list
  val get_method_approx: csenv -> string Binaryset.set Expr.CTypeSelectorsTab.table

  val is_exit_reachable: csenv -> string -> bool
  val update_hpfninfo0 : Absyn.ext_decl -> Absyn.ext_decl Symtab.table ->
                         Absyn.ext_decl Symtab.table
  val add_init_globals_fun: StmtDecl.statement list -> csenv -> csenv 
  val get_defined_functions : csenv -> Region.Wrap.region Symtab.table
  val get_read_globals : csenv -> modify_var Binaryset.set Symtab.table
  val is_recursivefn : csenv -> string -> bool
  val mvar_traverse : csenv -> csenv
  val get_modified_global_locns : csenv -> string Binaryset.set MVar_Table.table
  val get_all_globals : csenv -> int ctype MSymTab.table
  val get_untouched_globals : csenv -> int ctype MSymTab.table
  val get_touched_globinit_var_infos: csenv -> var_info list
  val fndes_callinfo : Proof.context -> string -> AstDatatype.gcc_attribute list Region.Wrap.t list -> 
        csenv -> expr -> fncall_type * (int ctype * int ctype list)

  val fns_by_type : csenv -> int ctype * int ctype list -> string list

  val cse_typing : {report_error:bool} -> Proof.context -> csenv -> expr -> int ctype

  val approx_expr : Proof.context -> csenv -> AstDatatype.expr_node ->
          (string * AstDatatype.var_info * selector list) list


  val used_fun_types_of_fun : csenv -> string -> int ctype list
  val uses_globals : csenv -> string -> bool
  val approx_globals': csenv ->
      (string * (selector list * (string * AstDatatype.var_info) list) list) list
  val approx_callees: csenv -> (string * Expr.var_info * selector list) -> string list
  val process_decls : Proof.context -> s2s_config -> Absyn.ext_decl list ->
                      ((Absyn.ext_decl list * Absyn.statement list) * csenv)
  val function_specs : csenv -> Absyn.fnspec list Symtab.table
  val sizeof_padding : csenv -> int ctype -> int * bool
  val sizeof : csenv -> int ctype -> int
  val sizeof_struct_or_union: csenv -> string -> int
  val is_packed : csenv -> int ctype -> bool
  val is_packed_trace : csenv -> int ctype -> bool
  val is_packed_struct_or_union : csenv -> string -> bool
  val is_packed_struct_or_union_trace : csenv -> string -> bool
  val alignof: csenv -> int ctype -> int
  val alignof_struct_or_union: csenv -> string -> int
  val offsetof: csenv -> string -> string -> int
  val offsetof': csenv -> string -> string list -> int
  val contains_packed_attr: senv -> int ctype -> bool

  val eq_string_assoc: (string * string list) list * (string * string list) list -> bool

  type asm_stmt_elements = (string * bool * expr option * expr list)
  val split_asm_stmt : Absyn.statement_node -> asm_stmt_elements
  val merge_asm_stmt : asm_stmt_elements -> Absyn.statement_node

  val get_globals_rcd : csenv -> senv

  val dest_method_fun_ptr: string -> {report_error:bool} -> Proof.context -> AstDatatype.gcc_attribute list Region.Wrap.t list -> 
        csenv -> Expr.expr -> (int CTypeDatatype.ctype * string) option

  val method_callers: csenv -> string list
  val method_callers_via_fun_ptr_param: csenv -> string list
  val method_callers_via_fun_ptr_param_of: csenv -> string -> string list
  val callers_via_fun_ptr_param: csenv -> string list
  val callers_via_local_fun_ptr_param: csenv -> string list
  val callers_via_fun_ptr_param_of: csenv -> string -> string list
  val callers_via_method_or_non_param_of_fun_ptr_param_of: csenv -> string -> string list

  val method_types: csenv -> (int ctype * int ctype list)  list
  val potential_method_callees: csenv -> string list (* functions matching method_types *)

  val approx_global_fun_ptrs_from_ty: csenv -> int CTypeDatatype.ctype * AstDatatype.selector list -> string list
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

  val check_post_ops_while: Proof.context -> Absyn.expr * AstDatatype.expr_node list -> unit
  val mk_post_op_assign: AstDatatype.expr_node -> Absyn.statement

  val variable_dependencies: Proof.context -> AstDatatype.dependencies Symtab.table -> csenv -> AstDatatype.dependencies Symtab.table
  val get_variable_dependencies: csenv -> AstDatatype.dependencies Symtab.table
  val map_variable_dependencies: (AstDatatype.dependencies Symtab.table -> AstDatatype.dependencies Symtab.table) -> csenv -> csenv
  val check_embedded_fncall_exprs: Proof.context -> csenv -> unit
  val check_packed_sizeof: bool Config.T
  val check_packed_align: bool Config.T
  val check_packed_offsets: bool Config.T
end

structure ProgramAnalysis: PROGRAM_ANALYSIS =
struct

fun maybe f opt = fold f (the_list opt)

open Absyn NameGeneration

type program = ext_decl list
type s2s_config = {anon_vars : bool, owners : string list,
                   allow_underscore_idents : bool, munge_info_fname : Path.T option, prog_name: string}

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


type 'a rcd_env = (string * (rcd_kind * (string wrap * 'a) list * Region.t * CType.attribute list)) list
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


type selector = Expr.selector
type fun_ptr_call_info = (int ctype * int ctype list) *
                         (string * AstDatatype.var_info * selector list) list * (* potentially called functions, or if selectors not null an object-method *)
                         bool (* true if C-style object method *)

datatype fncall_type = DirectCall of string
                     | FnPtrCall of fun_ptr_call_info

fun is_function (_:string, r:AstDatatype.var_info, _:selector list) = 
  (case !r of SOME (_, FunctionName) => true | _ => false)

fun triple_ord ord1 ord2 ord3 ((x1 ,y1, z1), (x2 ,y2, z2)) = 
  prod_ord ord1 (prod_ord ord2 ord3) ((x1, (y1, z1)), (x2, (y2, z2)))

val ty_ord = ctype_ord int_ord I
val funty_ord = prod_ord ty_ord (list_ord ty_ord)
fun fncall_ord (f1,f2) =
    case (f1, f2) of
      (DirectCall s1, DirectCall s2) => string_ord(s1, s2)
    | (DirectCall _, _) => LESS
    | (_, DirectCall _) => GREATER
    | (FnPtrCall (x1, x2, x3), FnPtrCall (y1, y2, y3)) =>
        prod_ord funty_ord (prod_ord (list_ord (triple_ord (string_ord) (AstDatatype.var_info_ord) selectors_ord)) bool_ord) 
         ((x1, (x2, x3)), (y1, (y2, y3)))

type callgraph =
  {callees: string Binaryset.set Symtab.table, callers: string Binaryset.set Symtab.table}

type embedded_fncall_exprs = (expr * fncall_type list) list Symtab.table


fun add_fncall_expr fname (fncall_type, expr) (tab: embedded_fncall_exprs) =
  let
    fun insert_fs [] = [fncall_type]
      | insert_fs (fs as (f::fs')) = if f = fncall_type then fs else f::insert_fs fs'

    fun insert [] = [(expr, [fncall_type])]
      | insert ((e as (expr1, fs))::es) = 
          if pointer_eq (expr1, expr) orelse (expr1 = expr) then (expr1, insert_fs fs)::es
          else e::insert es

  in
    case Symtab.lookup tab fname of 
      NONE => Symtab.update_new (fname, [(expr, [fncall_type])]) tab
    | SOME es => Symtab.update (fname, insert es) tab
  end

datatype clang_record_name = Named of string | Anonymous of SourcePos.t
datatype clang_field_kind = 
    Strct of {record_name: clang_record_name, field_name: string option} | 
    Un of {record_name: clang_record_name, field_name: string option} | 
    Fld of {name:string, typ:string}

type clang_field = {kind: clang_field_kind, level: int}
type clang_field_info = {field: clang_field, offset: int}
type clang_record_info = {
  header: clang_field_info,
  flds: clang_field_info list,
  size: int,
  align: int}


@{record \<open>
datatype csenv (* CalculateSatate environment *) = Csenv of
                 {prog_name: string,
                 senv : senv, union_variants: union_variants,  allow_underscore_idents : bool,
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
                 embedded_fncall_exprs: embedded_fncall_exprs,
                 recursive_functions : string Binaryset.set,
                 defined_functions : Region.Wrap.region Symtab.table,
                 modifies : modify_var Binaryset.set Symtab.table,
                 modify_locs : string Binaryset.set MVar_Table.table,
                 read_globals : modify_var Binaryset.set Symtab.table,
                 fnspecs : fnspec list Symtab.table,
                 owners : string list,
                 munge_info_fname : Path.T option,
                 constant_global_fun_ptrs: (string * string list) list,
                 fun_ptr_params: ((string * AstDatatype.var_info * selector list) list) option list Symtab.table, (* variables with which function pointer parameters are called*)
                 cliques : string list list,
                 fun_ptr_core_clique : string list,
                 method_approx: string Binaryset.set CTypeSelectorsTab.table,
                 final_callgraph : callgraph, 
                 final_callgraph_with_exit: callgraph, 
                 variable_dependencies: AstDatatype.dependencies Symtab.table,
                 clang_record_infos: clang_record_info list}
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

fun functions_with_local_fun_ptr_calls cse =
  [] |>
    Symtab.fold (fn (f, callees) => fn fs => 
        if null (filter (
          fn FnPtrCall (_, infos, _) => 
               exists (fn (_, info, _) => case !info of SOME (_, MungedVar {kind=Local, ...}) => true | _ => false) 
               infos
           | _ => false) (Binaryset.listItems callees)) then fs else f::fs)
      (get_call_info cse)

fun has_fun_ptr_calls cse fname =
  not (null (get_fun_ptr_calls cse fname))

fun functions_with_fun_ptr_calls cse =
  get_call_info cse |> Symtab.dest |> map_filter (fn (fname, callees) => 
    if exists (fn FnPtrCall x => true | _ => false) (Binaryset.listItems callees) then SOME fname else NONE)

fun get_fun_ptr_callees cse fname =
 get_fun_ptr_calls cse fname |> map #2 |> flat
 |> map_filter (fn (n, r, _) => case !r of SOME (_, FunctionName) => SOME n | _ => NONE)


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
    fun method_type (FnPtrCall ((retT, argTs), _, true)) = SOME (CType.Function (retT, argTs))
      | method_type _ = NONE
    val Ts = get_callgraph cse |> Symtab.dest |> maps (Binaryset.listItems o snd) 
      |> map_filter method_type |> sort_distinct (CType.ctype_ord int_ord I)
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

fun program_has_fun_ptr_calls cse =
  let
      val all_functions = get_functions cse
  in
    exists (has_fun_ptr_calls cse) all_functions
  end

fun get_max_function_arity cse = 
  0 
  |> Symtab.fold 
    (fn (_, (_, _, args)) => fn current_max => Int.max (current_max, length args))
    (get_fninfo cse) 

fun function_specs (Csenv {fnspecs,...}) = fnspecs

fun has_body_spec cse fname = exists (fn AstDatatype.gcc_attribs _ => false | _ => true)
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


fun emptycse ({anon_vars,owners,allow_underscore_idents = aui,munge_info_fname,prog_name,...} : s2s_config)=
    Csenv {
         prog_name = prog_name,
         senv = [], union_variants = [], anon_vars = anon_vars, allow_underscore_idents = aui,
         vars = Symtab.empty, mangled_vars = Symtab.empty,
         scope = [Symtab.empty],
         fninfo = Symtab.empty, hpfninfo = Symtab.empty,
         enumenv = ([],Symtab.empty),
         heaptypes = Binaryset.empty (ctype_ord int_ord I),
         usedtypes = Binaryset.empty (ctype_ord int_ord I),
         array_mentions = Binaryset.empty (prod_ord (ctype_ord int_ord I) int_ord),
         call_info = Symtab.empty,
         caller_info = Symtab.empty,
         referenced_funs = Symtab.empty,
         addressed = XMSymTab.empty,
         addressed_types = Absyn.CTypeTab.empty,
         defined_functions = Symtab.empty,
         embedded_fncalls = Binaryset.empty fncall_ord,
         embedded_fncall_exprs = Symtab.empty,
         recursive_functions = Binaryset.empty string_ord,
         modifies = Symtab.empty, modify_locs = MVar_Table.empty,
         fnspecs = Symtab.empty, read_globals = Symtab.empty,
         globinits = MSymTab.empty, owners = owners, munge_info_fname = munge_info_fname, 
         constant_global_fun_ptrs = [], cliques = [], fun_ptr_core_clique = [], fun_ptr_params = Symtab.empty, 
         method_approx =  CTypeSelectorsTab.empty,
         final_callgraph = {callees = Symtab.empty, callers = Symtab.empty},
         final_callgraph_with_exit = {callees = Symtab.empty, callers = Symtab.empty},
         variable_dependencies = Symtab.empty,
         clang_record_infos = []}

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

val init_globals_var_info = Var_info {name = NameGeneration.init_globalsN, vtype = Function (Void, []),
     munged_name = MString.mk (NameGeneration.init_globalsN),
     proto_param = false, struct_env = [], fname = NONE, return_var = false, attrs = [],
     declared_at = Region.bogus, method_call_tmp_var = false}


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

fun new_embedded_fncall fname root_expr s cse =
   let
   in
     map_embedded_fncalls (fn set => Binaryset.add(set,s)) cse |>
     map_embedded_fncall_exprs (add_fncall_expr fname (s, root_expr))
   end

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

fun get_all_globals cse = let
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

fun get_untouched_globals cse = let
  open MSymTab
  fun mydelete (t,e) = delete_safe e t
  val all_globals = get_all_globals cse
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

fun get_touched_globinit_var_infos cse =
  let
    val globinits = get_globinits cse |> MSymTab.dest |> map (fst)
    val untouched_globals = get_untouched_globals cse |> MSymTab.dest |> map (fst)
    val touched_globals = subtract (op =) untouched_globals globinits
    val globals = get_globals cse
    fun get_var_info g = find_first (fn vi => get_mname vi = g) globals
    val var_infos = map (the o get_var_info) touched_globals
  in
    var_infos
  end


fun get_vi_nm_info (Csenv cse) (Var_info {name, munged_name, ...}) : nm_info =
    let
    in
      {src_name = name, isa_name = munged_name}
    end

(* ML computation of alignment and type sizes *)
val ti  = IntInf.toInt

fun roundup base n = if n mod base = 0 then (n, false) else ((n div base + 1) * base, true)
fun maxl [] = 0
  | maxl (h::t) = let val m = maxl t in if h > m then h else m end

val check_packed_sizeof = Attrib.setup_config_bool \<^binding>\<open>c_parser_check_packed_sizeof\<close> (K true)
val check_packed_align = Attrib.setup_config_bool \<^binding>\<open>c_parser_check_packed_align\<close> (K true)
val check_packed_offsets = Attrib.setup_config_bool \<^binding>\<open>c_parser_check_packed_offsets\<close> (K true)

fun alignof_attrs [] = NONE
  | alignof_attrs (AlignedExponent i::_) = SOME (IntInf.pow(2, i))
  | alignof_attrs (Packed::xs) = alignof_attrs xs
 
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
        Signed i => int_alignof i
      | Unsigned i => int_alignof i
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
      | Bitfield _ => int_alignof Int
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

fun gen_offset (trace:bool) strict cse tylist n =
  let
    val offset = gen_offset trace strict cse
  in
    if n = 0 then (0, false)
    else if length tylist <= n then (0, false)
    else
      let
        val (offn', padding0) = offset tylist (n - 1)
        val _ = if trace then tracing ("offset: offset tylist " ^ @{make_string} (n - 1) ^ ": " ^ @{make_string} (offn', padding0, tylist)) else ()
        val tyn' = #1 (List.nth(tylist, n - 1))
        val tyn = List.nth(tylist, n)
        val (sz', padding') = gen_sizeof trace strict cse tyn'
        val _ = if trace then tracing ("offset: gen_sizeof trace strict cse " ^ @{make_string} tyn' ^ ": " ^ @{make_string} (sz', padding')) else ()
        val b = offn' + sz'
        val (res, padding1) = roundup (gen_alignof cse tyn) b
        val _ = if trace then tracing ("offset: roundup (gen_alignof cse " ^ @{make_string} tyn ^ ") " ^ @{make_string} b ^ ": " ^ @{make_string} (res, padding1)) else ()
        val res_padding = padding0 orelse padding' orelse padding1
        val _ = if trace then tracing ("offset res, res_padding: " ^ @{make_string} (res, res_padding)) else () 
      in
        (res, res_padding)
      end
  end
and gen_strsize (trace:bool) strict cse s : (Int.int * bool) =
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
          val (off, padding1) = gen_offset trace strict cse tys' lastn
          val _ = if trace then tracing ("strsize Struct: offset tys' " ^ @{make_string} tys' ^ " " ^ @{make_string} lastn ^ ": " ^ @{make_string} (off, padding1)) else ()
          val a = maxl (algn :: (map (gen_alignof cse) tys'))
          val (sz', padding2) = gen_sizeof trace strict cse lastty
          val _ = if trace then tracing ("strsize Struct: sizeof lastty " ^ @{make_string} lastty ^ ": " ^ @{make_string} (sz', padding2)) else ()
          val (res, padding3) = roundup a (off + sz')
          val _ = if trace then tracing ("strsize Struct: roundup " ^ @{make_string} a ^ " " ^ @{make_string} (off + sz') ^ ": " ^ @{make_string} (res, padding3)) else ()
          val res_padding = padding1 orelse padding2 orelse padding3
          val _ = if trace then tracing ("strsize Struct: res, res_padding: " ^ @{make_string} (res, res_padding)) else () 
        in
          (res, res_padding)
        end
    | Union active =>
        let
          fun error_msg sizes flds = Pretty.block (
                [Pretty.str  ("different variants of union " ^ quote s ^ " don't have same size: ")] @
                [Pretty.list "" ""  (map (fn ((n, _), size) => Pretty.str (node n ^ ": " ^ string_of_int size)) (flds ~~ sizes))])
            |> Pretty.string_of
          val fld_sizes_paddings = map (fn (s, (t, _)) => (node s, gen_sizeof trace strict cse t)) flds
          val fld_sizes = map (apsnd fst) fld_sizes_paddings
          val paddings = map (#2 o #2) fld_sizes_paddings
          val _ = if trace then tracing ("strsize Union: paddings: " ^ @{make_string} paddings) else () 
          val variant_padding = exists I paddings
          val _ = if trace then tracing ("strsize Union: variant_padding: " ^ @{make_string} variant_padding) else () 
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
          val _ = if trace then tracing ("strsize Union: roundup " ^ @{make_string} a ^ " " ^ @{make_string} size ^ ": " ^ @{make_string} (res, padding)) else ()
          val res_padding = variant_padding orelse padding
          val _ = if trace then tracing ("strsize Union: res, res_padding: " ^ @{make_string} (res, res_padding)) else () 
        in
          (res, res_padding)
        end
  end
and gen_sizeof trace strict cse ty = Absyn.sizeof (gen_strsize trace strict cse) ty

val sizeof_padding = gen_sizeof false false
val sizeof_padding_trace = gen_sizeof true false
val sizeof = fst oo sizeof_padding
val is_padding = snd oo sizeof_padding
val is_padding_trace = snd oo sizeof_padding_trace
val is_packed = not oo is_padding
val is_packed_trace = not oo is_padding_trace
val offset_padding = gen_offset false false
val offset = fst ooo offset_padding
val strsize = gen_strsize false false
fun alignof cse ty = gen_alignof cse (ty,[])

fun offsetof cse s fld =
  let
    val (kind, fields, _, _) = get_record_info cse s
    val idx = find_index (fn (n, _) => node n = fld) fields
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
        case find_first (fn (n, _) => node n = fld) fields of
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
fun is_packed_struct_or_union cse s = is_packed cse (type_of_struct_or_union cse s)
fun is_packed_struct_or_union_trace cse s = is_packed_trace cse (type_of_struct_or_union cse s)

fun cse2ecenv ctxt cse = CE {enumenv = get_enumenv cse,
                        typing = cse_typing {report_error = true} ctxt cse,
                        structsize = strsize cse,
                        offset_of = offsetof' cse}
and cse_typing report_error ctxt cse e = let
  val scopes = get_scope cse
  fun var_typing [] _ = NONE
    | var_typing (tab::rest) s =
      case Symtab.lookup tab s of
        NONE => var_typing rest s
      | SOME vi => SOME (get_vtype vi)
                    handle Empty => raise Fail "Empty vi-list in cse_typing"
in
  ExpressionTyping.expr_type report_error ctxt (cse2ecenv ctxt cse)
                              (get_senv cse)
                              (var_typing scopes)
                              e
end

local
open AstDatatype

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
  | dest_access ctxt ecenv (Deref (E e)) = dest_access ctxt ecenv (node e)
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
        val accss = fld_tys |> map (fn (fld, ty) => map (cons (Field (node fld))) accss) |> flat
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
    val res = try (dest_access ctxt ecenv) e
    fun empty_accs (x, y) = (x, y, [])
  in
    res
    |> Option.map (fn ((v, info), accs) =>
         (case MSymTab.lookup (get_globinits cse) (MString.mk v) of
           SOME e => dest_init_expr e |> approx_literal_access accs |> map empty_accs
          | NONE => [(v,info, accs)] ))
    |> these
  end

fun approx_ctyp (_, info_ref, selectors) = 
  case !info_ref of
    SOME (ty, _) => SOME (ty, selectors)
  | _ => NONE

fun approx_literal_access' accs inits = (accs, approx_literal_access accs inits)

fun approx_globals' cse =
  let
    val senv = get_senv cse
    val vars = get_variables cse NONE
    fun lookup g = find_first (fn vi => get_munged_name vi = g) vars
    fun typ_of g = lookup g |> the |> get_vtype
    fun approx (g, e) =
      let
        val inits = dest_init_expr e
        val accss = all_accesses senv (typ_of g)
      in ( MString.dest g, accss |> map (fn accs => approx_literal_access' accs inits) ) end
  in
    MSymTab.dest (get_globinits cse)
    |> map approx
  end


fun approx_globals cse =
  approx_globals' cse |> map (fn (x, is) => (x, maps snd is))

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


fun add_method_approx (ctyp, selectors) fname =
  map_method_approx (
    CTypeSelectorsTab.map_default ((ctyp, map Expr.norm_index selectors), Binaryset.empty fast_string_ord) 
      (fn fs => Binaryset.add (fs, fname)))

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

fun dest_fun ctxt (resT, argTs) fe =
  let
    val region = Region.make{left = eleft fe, right = eright fe}
    val error = fn s => Feedback.error_region ctxt region (": " ^ s)

  in
    case enode fe of
      Var (name, more_info) => 
        (case !more_info of
           SOME (T as Function _, FunctionName) =>
             let 
               val expectedT = Function (resT, argTs)
               
             in 
               if CType.norm_enum expectedT = CType.norm_enum T then 
                 name 
               else
                error ("types of function " ^ quote name ^ " does not match expected function pointer type:\n " ^ 
                  "expected: " ^ @{make_string} expectedT ^ "\n" ^ 
                  name ^ ": " ^ @{make_string} T)
             end
         | _ => error ("variable " ^ quote name ^ " is not a function. Expection function in 'calls' attribute."))
    | _ => error "expecting function name in 'calls' attribute"
  end

fun is_calls_attr (GCC_AttribFn ("calls", fs)) = true
  | is_calls_attr _ = false

fun dest_calls_attr ctxt (resT, argTs) (GCC_AttribFn ("calls", fs)) = SOME (map (dest_fun ctxt (resT, argTs)) fs)
  | dest_calls_attr _ _ _ = NONE

fun dest_call_attrs ctxt (resT, argTs) [] = NONE
  | dest_call_attrs ctxt (resT, argTs) (attrs::_) = map_filter (dest_calls_attr ctxt (resT, argTs)) (node attrs) |> 
     (fn ass => if null ass then NONE else SOME (flat ass))

fun mk_callee_info (resT, argTs) name = (name, Unsynchronized.ref (SOME (Function (resT, argTs), FunctionName)), [])

fun approx_expr_attrs ctxt attrss (resT, argTs) cse e =
  case dest_call_attrs ctxt (resT, argTs) attrss of
    NONE => approx_expr ctxt cse e
  | SOME funs =>  map (mk_callee_info (resT, argTs)) funs
 

fun raw_fndes_callinfo (re as {report_error}) ctxt attrss cse e =
   let
     val ctxt = ctxt |> report_error = false ? Config.put Feedback.feedback_as_error true
     val typ = cse_typing re ctxt cse e
   in
    case (typ, enode e) of
      (Function x, Var(s, _)) =>
        let
        in
          (DirectCall s, x)
        end
    | (ty, e') => let
      in
        case ty of
          Function x => (FnPtrCall (x, approx_expr_attrs ctxt attrss x cse e', false), x)
        | Ptr (Function x) =>
            (FnPtrCall (x, approx_expr_attrs ctxt attrss x cse e', false ), x)
        | _ => if report_error then eFail ctxt (e, "Function designator has bad type ("^
                               tyname ty ^ ")")
               else error ("Function designator has bad type ("^
                               tyname ty ^ ")")
      end
  end

fun get_local_info cse (n, NONE) = NONE
  | get_local_info cse (loc as (n, SOME fname)) =
  let
    val addressed = XMSymTab.defined (get_addressed cse) loc
    val vars = get_variables cse (SOME fname)
    fun match vi = MString.eq (get_mname vi, n)
    val params = get_params fname cse |> these
    val i = find_index match params
    val res =   
      if 0 <= i then SOME {kind = NameGeneration.In i, addressed = addressed, info = nth params i}
      else find_first match vars |> Option.map (fn info => {kind=NameGeneration.Loc, addressed= addressed, info= info})
  in
    res
  end

fun variable_info_from_var_info (Loc) = Local
  | variable_info_from_var_info (In i) = Parameter i
  | variable_info_from_var_info (Out) = error ("variable_info_from_var_info: unexpected Out")

 
fun get_variable_info cse vi = 
  if is_global vi then SOME (Global) 
  else get_local_info cse (get_munged_name vi, get_fname vi) |> Option.map (variable_info_from_var_info o #kind)

fun the_variable_info cse vi =
  case get_variable_info cse vi of
    SOME x => x
  | NONE => error ("the_variable_info: unexpected term" ^ @{make_string} vi)

fun is_function_var var_info = 
  (case !var_info of
    SOME (_, FunctionName) => true
  | _ => false)

fun dest_method_fun_ptr caller report_error ctxt attrss cse fn_e =
  (case try (raw_fndes_callinfo report_error ctxt attrss cse) fn_e of
    SOME (FnPtrCall ((retT, argTs), funs, _), _) => 
      (case Expr.vars_expr {typ = false, addr = false, pre_op=true, post_op = true} fn_e of
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
       | xs as ((_, root_var_info)::_) =>
          if is_function_var root_var_info then (* can't be the global dispatcher case *)
            SOME (Ptr (Function (retT, argTs)), caller) 
          else 
            NONE (* could be global dispatcher case *) 
       | [] => NONE)
  | _ => NONE)

fun fndes_callinfo ctxt caller attrss cse fn_e =
  case raw_fndes_callinfo {report_error = true} ctxt attrss cse fn_e of
    (FnPtrCall (ty, fs, false), x) => (FnPtrCall (ty, fs, is_some (dest_method_fun_ptr caller {report_error = true} ctxt attrss cse fn_e)), x)
  | res => res
 

fun process_enumdecl ctxt (enameopt_w,econsts) env = let
  fun mk_ecenv (set, enum_tab) = CE {enumenv = enum_tab,
          typing = cse_typing {report_error = true} ctxt env, structsize = strsize env, offset_of = offsetof' env}
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

fun is_packed_gcc_attr (GCC_AttribID "packed") = true
  | is_packed_gcc_attr _ = false

fun is_packed_attr (Packed) = true
  | is_packed_attr _ = false

fun newstr_decl process_expr ctxt (kind: rcd_kind) (nm, flds0 : (expr ctype * string wrap * gcc_attribute list) list, sattrs0) cse = let
  open NameGeneration
  fun foldthis (cty,fldnm,attrs) acc =
      process_type process_expr ctxt (left fldnm, right fldnm) cty acc
  val cse = cse |> fold foldthis flds0
  val n_flds = length flds0
  val flexible_array_fields = 
    map_index (fn (x as (i, (cty,_,_))) => if flexible_array_type cty then SOME x else NONE) flds0
    |> map_filter I
  val _ = null flexible_array_fields 
          orelse
          (kind = Struct andalso n_flds > 1 andalso 
            length flexible_array_fields = 1 andalso #1 (hd flexible_array_fields) = n_flds - 1)
          orelse
            let
              val (fld, l, r) = (unwrap o #2 o #2) (hd flexible_array_fields)
            in
              Feedback.error_range ctxt l r 
                ("flexible array member " ^ quote fld ^ " only allowed as last field in a non-empty struct")
            end
  
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

  val packed_attrs = if exists is_packed_gcc_attr (node sattrs0) then [Packed] else []
  val sattrs1 = [] |> fold (add_aligned (left sattrs0) (right sattrs0)) (node sattrs0)
  val sattrs = sattrs1 @ packed_attrs

  val flds =
      map (fn (ty,s,attrs) =>
              ((uscore_check unC_field_name "field" s; s),
               (remove_enums (constify_abtype true ctxt ecenv ty), [] |> fold (add_aligned (left nm) (right nm)) attrs)
               ))
          flds0
  val _ = uscore_check unC_struct_name "tag" nm
  val l = left nm 
  val r' = right nm
  val r = Region.make {left=l, right=r'}
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

fun new_scope cse = map_scope (fn l => Symtab.empty :: l) cse
fun pop_scope cse = map_scope tl cse
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


fun insert_var ctxt (v as Var_info {name, vtype, fname, declared_at, ...}, e as Csenv cse) = let
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
         raise Feedback.error_region ctxt declared_at ("Variable "^name^ " " ^ fnToString fname ^
                     " declared twice (no scope-masking allowed)")

    end
end

fun inits_to_elist f (InitE e) acc = List.rev (f e :: acc)
  | inits_to_elist f (InitList dis) acc =
       acc |> fold (fn (_, i) => fn a => inits_to_elist f i a) dis
      
fun dest_statement_expression ctxt e =
  case enode e of
    StmtExpr (bl, SOME e) => (bl, e)
  | StmtExpr (_, NONE) => Feedback.error_range ctxt (eleft e) (eright e) "gcc style statement-expression must end with an expression"
  | EFnCall(_) => ([], map_origin (K AstDatatype.Statement) e)
  | _ => ([], e)

structure TypeTab = Table(type key = int ctype
                          val ord = ctype_ord int_ord I);

datatype lvstate = LV | RV

(* fname is a string option; NONE corresponds to an expression appearing at
   the global level, as can happen in the initialisation of a global *)
fun process_expr ctxt lvstate fname attrss (env as Csenv {senv, ...}) e = let
  val root_expr = e;
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
  fun pex e env = fst (process_expr ctxt lvstate fname attrss env e)
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
          val acc = if scp andalso (has_post_effects ctxt e1 orelse eneeds_sc_protection e2) andalso
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
      | PostOp(e1, _) => count_fncalls (rval ef) (E e1::es)
      | PreOp(e1, _) => count_fncalls (rval ef) (E e1::es)
      | CondExp(e1,e2,e3) => let
          val acc =
              if adstat <> SzOf andalso
                 (has_post_effects ctxt e1 orelse eneeds_sc_protection e2 orelse eneeds_sc_protection e3)
              then let
                  val ty1 = cse_typing {report_error=true} ctxt env e2
                  val ty2 = cse_typing {report_error=true} ctxt env e3
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
                         fname = fname, init = the_default false (Option.mapPartial (get_init o snd) (!vinfo_ref)),
                         kind = the_variable_info env vi
                       })
            in
              vinfo_ref := SOME (ty, info);
              count_fncalls (env,fmap,adstat) es
            end
        end
      | StructDot(e1, field) =>
        let
          val ty1 = cse_typing {report_error=true} ctxt env e1
        in   
          case ExpressionTyping.expand_anonymous_field' senv ty1 e1 field of 
            SOME e' => count_fncall ef e' es
          | NONE => 
            let         
              val ty = cse_typing {report_error=true} ctxt env e
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
      end
      | ArrayDeref(e1,e2) => let
          val ty = cse_typing {report_error=true} ctxt env e
          val ty1 = cse_typing {report_error=true} ctxt env e1
          val env = if ptr_type ty1 andalso is_some fname andalso
                       not (lvadstat adstat) andalso adstat <> SzOf
                    then
                      add_read (the fname) TheHeap env
                    else env
        in
          case adstat of
            UnderAddr sels => count_fncalls (env,fmap,extend_selector (Index NONE) (BL_Addr sels))
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
          | BL_Addr sels => count_fncalls (env,fmap,extend_selector (Index NONE) (BL_Addr sels))
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
          val ty = case cse_typing {report_error=true} ctxt env e1 of
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
      | EFnCall(origin, fn_e, args) => let
          val env = pex fn_e env
          fun tempvar_if_postops e fmap =
            if has_post_effects ctxt e then 
              let
                val ty = cse_typing {report_error=true} ctxt env e
              in inc(fmap, ty) end
            else fmap

          val (callee, (rettyp, _)) = fndes_callinfo ctxt (fname_str fname) attrss env fn_e
          val fmap = the_default fmap (dest_method_fun_ptr (fname_str fname) {report_error=true} ctxt attrss env fn_e |> Option.map (fn (fun_ptrT, fname) =>
                       inc(fmap, fun_ptrT)))
          val env = if adstat <> SzOf then
                      new_call ctxt {caller = fname_str fname, callee = callee, args = args} env
                    else env
          val env = if adstat <> SzOf andalso origin = AstDatatype.Expression then new_embedded_fncall (fname_str fname) root_expr callee env
                    else env
          val stat' = if adstat <> SzOf then Rvalue else SzOf
          val fmap' = inc(fmap,rettyp) |> fold tempvar_if_postops args
        in
          count_fncalls (env,fmap',stat')
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
      | AssignE (origin, e1, e2) => count_fncalls ef ([RAS Lvalue, E e1, RAS Rvalue, E e2] @ 
          (if origin = AstDatatype.Expression then [RAS Lvalue, E e1] else []) @
          RAS adstat::es)
      | Comma (e1, e2) => 
         let 
           val ty1 = cse_typing {report_error=true} ctxt env e1
           val acc = (env, inc(fmap, ty1), adstat)
         in count_fncalls acc (E e1::E e2::es) end
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
  val senv = get_senv env
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
      | StructDot (e', fld) => 
        let
          val ty_e = cse_typing {report_error=true} ctxt env e
        in 
          case ExpressionTyping.expand_anonymous_field' senv ty_e e fld of 
            SOME e' => recurse state e'
          | NONE =>
            let
            in
              case ty_e of
                Ptr _ => if state = BrackLeft then SOME TheHeap
                         else recurse state e'
              | _ => recurse state e'
            end
        end
      | ArrayDeref (e', _) => recurse BrackLeft e'
      | Deref _ => SOME TheHeap
      | TypeCast (_, e') => recurse state e'
      | _ => NONE
in
  recurse Normal e
end


fun fcall_retty_disagrees ctxt caller attrss env fn_e args lvtyp = let
    val (_, (retty, _)) = fndes_callinfo ctxt caller attrss env fn_e
  in lvtyp <> retty end

(* treat some problematic function calls as embedded. this detects whether the
   lvar is compound or type promotion would be required. either case would
   result in a nonstandard CALL element once translated. tweaking the function
   call into an embedded EFnCall causes it to be separated into an additional
   standard CALL statement later. *)
fun treat_as_emb_fcall ctxt caller attrss env (NONE,fn_e,args) = false
  | treat_as_emb_fcall ctxt caller attrss env (SOME lv,fn_e,args) = let
    val lvtyp = cse_typing {report_error=true} ctxt env lv
    val lv_plain = case enode lv of Var _ => true | _ => false
  in not lv_plain orelse fcall_retty_disagrees ctxt caller attrss env fn_e args lvtyp end

fun treat_ret_as_emb_fcall ctxt caller attrss env (NONE,fn_e,args) = false
  | treat_ret_as_emb_fcall ctxt caller attrss env (SOME retty,fn_e,args)
    = fcall_retty_disagrees ctxt caller attrss env fn_e args retty

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

fun mk_post_op_assign (PostOp (e, m)) =
  let
    val l = eleft e
    val r = eright e
    val operation = case m of Plus_Plus => Plus | Minus_Minus => Minus
    val binop = ewrap (BinOp (operation, e, expr_int 1), l, r)
  in
    swrap (Assign (e, binop), l, r)
  end
  | mk_post_op_assign t = error ("mk_post_op_assign: unexpected term: " ^ @{make_string} t)

fun check_local_var ctxt e =
  let
    val l = eleft e
    val r = eright e
  in 
  case vars_expr {typ=false, addr=false, post_op=false, pre_op=false} e of
    [] => Feedback.error_range ctxt l r "undefined behavior: side effects only allowed on local variables"
  | [var] => 
      (case dest_var var of 
        SOME (info as (_, (_, {kind, ...}))) => 
          if not (is_global_variable kind) then (info, l, r) else Feedback.error_range ctxt l r "undefined behavior: side effects only allowed on local variables"
       | _ => Feedback.error_range ctxt l r "undefined behavior: side effects only allowed on local variables")
  | vars => Feedback.error_range ctxt l r "undefined behavior: expecting single local variable here"

  end

fun check_post_ops ctxt ops1 ops2 =
  let
    val ops = ops1 @ ops2
    val ops'  = map_filter dest_post_op' ops
    val _ = if length ops' <> length ops then error "check_post_ops: expection only PostOp" else ()
    val local_vars = map (check_local_var ctxt o fst) ops'
    val dups = duplicates ((op =) o apply2 #1) local_vars
    val _ = case dups of [] => () | 
              (((x,_), l, r)::_) => 
                Feedback.error_range ctxt l r ("undefined behavior: duplicate variable with side effects: " ^ quote x)
  in
    chop (length ops1) local_vars
  end

fun check_post_ops_while ctxt (e, post_ops) =
  let
    val (_, vars_post_ops) = check_post_ops ctxt [] post_ops
    val e_vars = vars_expr {typ=false, addr=false, pre_op=false, post_op=false} e |> map_filter dest_var
    val inter1 = inter (fn ((x,_,_), y) => x=y) (e_vars) (vars_post_ops)
    val _ = case inter1 of [] => () | ((v, l, r)::_) =>
      Feedback.error_range ctxt l r "undefined behavior: variable collision with side effects"
  in
    ()
  end

fun check_post_ops_assign ctxt (left, left_post_ops) (right, right_post_ops) =
  let
    val (vars_post_left, vars_post_right) = check_post_ops ctxt left_post_ops right_post_ops
    val left_vars = vars_expr {typ=false, addr=false, pre_op=false, post_op=false} left |> map_filter dest_var
    val right_vars = vars_expr {typ=false, addr=false, pre_op=false, post_op=false} right |> map_filter dest_var

    val inter3 = inter (fn ((x,_,_), y) => x=y) (left_vars @ right_vars) (vars_post_left @ vars_post_right)
    val _ = case inter3 of [] => () | ((v, l, r)::_) =>
      Feedback.error_range ctxt l r "undefined behavior: variable collision with side effects"
    val inter1 = inter (fn ((x,_,_), y) => x=y) (right_vars) vars_post_left
    val _ = case inter1 of [] => () | ((v, l, r)::_) =>
      Feedback.error_range ctxt l r "undefined behavior: variable also appears in right hand side of assignment"
    val inter2 = inter (fn ((x,_,_), y) => x=y) (left_vars) vars_post_right
    val _ = case inter2 of [] => () | ((v, l, r)::_) =>
      Feedback.error_range ctxt l r "undefined behavior: variable also appears in left hand side of assignment"

  in
    ()
  end

fun mk_while_with_post_ops l r e post_ops inv bdy =
  case post_ops of [] => error ("mk_while_with_post_ops: empty list")
  | _ => let
    (* E.g. 
      while(n--) {...}   
      \<longrightarrow> 
      while (1) {
         if (n) { n--} else {n--; break;}; 
         ... 
         }
     *)
           val le = eleft e
           val re = eright e
           fun s x = swrap (x, le, re)
           fun b x = swrap (x, SourcePos.bogus, SourcePos.bogus)
           fun blk xs = Block (AstDatatype.Closed, map BI_Stmt xs)
           val assigns = map mk_post_op_assign post_ops

           val cond_sideeffect = s (IfStmt (e, s (blk assigns), s(blk (assigns @ [b Break]))))
           val bdy' = s (blk [cond_sideeffect, bdy])
           val while' = swrap (While(expr_int 1, inv, bdy'), l, r)
         in
           swrap (Trap (BreakT, while'), l, r)
         end

fun check_return ctxt l r (SOME (BI_Stmt stmt)) =
    (case snode stmt of
         Return _ => ()
    | _ => Feedback.error_range ctxt l r ("nested switch statement must end in default case and each case must end in a return"))
  | check_return ctxt l r NONE (* comes from a break *) = Feedback.error_range ctxt l r ("nested Switch must have default case and each case must end in a return")
  | check_return _ _ _ _ = ()

fun check_default_dummy_case ctxt l r ([NONE], [BI_Stmt stmt]) = 
    (case snode stmt of
       EmptyStmt  => (* If no default statement was in the sources this was inserted *)
         Feedback.error_range ctxt l r ("nested switch statement must end in default case, which has to end in a return")
    | _ => ())
  | check_default_dummy_case _ _ _ _ = ()

fun check_nested_switch ctxt [BI_Stmt stmt1] =
  (case snode stmt1 of
    Trap (BreakT, stmt2) => 
      (case snode stmt2 of
         Switch (e, nested_cases) => 
           let
             val l = sleft stmt2
             val r = sright stmt2
             val case_stmts = map snd nested_cases
             val _ = map (check_nested_switch ctxt) case_stmts
             val (_, (last as (last_exprs, _))) = split_last nested_cases
             val _ = check_default_dummy_case ctxt l r last
             val (_, last_case) = split_last last_exprs
             val last_stmts = map last_blockitem case_stmts
             val _ = map (check_return ctxt l r) last_stmts
             val _ = 
               (case last_case of 
                 NONE => ()
               | SOME (case_expr) => Feedback.error_range ctxt (eleft case_expr) (eright case_expr) ("nested switch statement must end in default case"))

           in () end
        | _ => ())
   | _ => ())
  | check_nested_switch _ _ = ()

fun wrap_block l r bl stmts =
  if null bl then 
    stmts
  else
    [swrap (Block (AstDatatype.Closed, bl @ map BI_Stmt stmts), l, r)]

fun gen_add_modify_var m x = 
  let
    open AstDatatype
  in
    case m of
       M info => 
         if is_global info then 
           if function_type (get_vtype info) then 
             x 
           else
             map_global_vars (Symuset.insert (srcname info)) x 
         else x 
    | AllGlobals => map_global_vars (K Symuset.univ) x  
    | TheHeap => map_heap_vars (bool_insert true) x
    | PhantomState => map_global_vars (Symuset.insert (NameGeneration.phantom_state_name)) x
    | _ => x
  end

fun closure deps names =
  let
    val emp =  Binaryset.empty String.compare
    val init = Binaryset.addList (emp, names)
    fun step f = the_default emp (Symtab.lookup deps f)
    val all = Binaryset.closure step init
  in all end

fun get_final_callers cse fnames =
  let
    val callers = #callers (get_final_callgraph cse)
  in
    Binaryset.listItems (closure callers fnames)
  end

fun get_final_callees cse fnames =
  let
    val callees = #callees (get_final_callgraph cse)
  in
    Binaryset.listItems (closure callees fnames)
  end

val assume_prototypes_pure = Attrib.setup_config_bool \<^binding>\<open>c_parser_assume_prototypes_pure\<close> (K false)

fun attrib_const (GCC_AttribID "StrictC'__const__") = true
  | attrib_const (GCC_AttribID "const") = true
  | attrib_const _ = false
fun attrib_pure (GCC_AttribID "StrictC'__pure__") = true
  | attrib_pure (GCC_AttribID "pure") = true
  | attrib_pure _ = false

fun proto_deps ctxt csenv proto_defaults f =
  let
    open AstDatatype
    val emp = deps_empty
    val add = gen_add_modify_var           
    fun add_mvars vs = 
      fold add (Binaryset.listItems vs)
    val fninfo = get_fninfo csenv
    val is_proto = the_default false (Symtab.lookup fninfo f |> Option.map #2)
  in
    if not is_proto then NONE 
    else
      (case Symtab.lookup proto_defaults f of
         SOME deps => SOME deps
      | NONE => 
          (case get_fun_modifies csenv f of
            SOME modifies => SOME (emp 
               |> map_write (add_mvars modifies) |> map_read (add_mvars modifies))
          | NONE => 
            let
              val fnspecs = get_fnspecs csenv
              val attribs = the_default [] (Symtab.lookup fnspecs f |> Option.map (
                map_filter (fn AstDatatype.gcc_attribs attrs => SOME attrs | _ => NONE) #> flat))

              val is_pure = exists attrib_const attribs
              val is_read_only = exists attrib_pure attribs
              val deps = 
                if is_read_only then 
                  AstDatatype.prototype_read_only_dependencies
                else if is_pure then
                  AstDatatype.prototype_pure_dependencies
                else if Config.get ctxt assume_prototypes_pure then 
                  prototype_pure_dependencies 
                else prototype_default_dependencies
            in 
              SOME deps
            end)) 
  end   
fun variable_dependencies ctxt proto_defaults csenv =
  let
    open AstDatatype
    val e = Binaryset.empty mvar_compare
    val emp = deps_empty
    val cliques = get_cliques csenv
    val add = gen_add_modify_var           
    fun add_mvars vs = 
      fold add (Binaryset.listItems vs)
 
    fun deps_body f =
      case proto_deps ctxt csenv proto_defaults f of
        SOME d => d
      | _ =>
        let
          val modifies = the_default e (get_fun_modifies csenv f)
          val read_globals = the_default e (Symtab.lookup (get_read_globals csenv) f)
        in
          emp 
          |> map_write (add_mvars modifies)
          |> map_read (add_mvars read_globals)
        end
    fun deps_clique_callees clique tab =
      let
        val clique_callees = get_final_callees csenv clique |> filter_out (member (op =) clique)
        fun deps f = case Symtab.lookup tab f of SOME x => x 
          | NONE => error ("variable_dependencies: callees should already be anaylsed: " ^ @{make_string} f)
        val res = deps_unions (map deps clique_callees)
      in
        res
      end
    fun deps_clique clique tab =
      let
        val body_deps = deps_unions (map deps_body clique)
        val callee_deps = deps_clique_callees clique tab
        val d = deps_union body_deps callee_deps
      in
        tab |> fold (fn f => Symtab.update_new (f, d)) clique
      end
    val res = Symtab.empty |> fold deps_clique cliques
  in
    res
  end


fun is_seq_bop (LogOr) = true
  | is_seq_bop (LogAnd) = true
  | is_seq_bop _ = false

fun check_overlap ctxt (e_opt: expr option) (d1, l) (d2, r) =
  let
    open AstDatatype
    fun err msg vars = Feedback.error_range ctxt l r 
      ("overlapping " ^ msg ^ " in expression:\n " ^ @{make_string} vars ^ 
        "\n d1: " ^ @{make_string} d1 ^
        "\n d2: " ^ @{make_string} d2 ^ 
        (case e_opt of SOME e => "\n e: "  ^ @{make_string} e | _ => ""))
    val inter_writes = vars_inter (get_write d1) (get_write d2)
    val _ = vars_is_empty inter_writes orelse err "writes-writes" inter_writes
    val inter_writes_reads = vars_inter (get_write d1) (get_read d2)
    val _ = vars_is_empty inter_writes_reads orelse err "writes-reads" inter_writes_reads
    val inter_reads_writes = vars_inter (get_read d1) (get_write d2)
    val _ = vars_is_empty inter_reads_writes orelse err "reads-writes" inter_reads_writes
  in
    deps_union d1 d2
  end

datatype mode = RValue | LValue | Address

fun check_expression_dependencies ctxt deps_opt cse (m as {mode:mode}) e =
  let
    val ctype_of = cse_typing {report_error=false} ctxt cse
    val check' = check_expression_dependencies ctxt deps_opt cse
    val check = check' m
    val check_i = check_initializer_dependencies ctxt deps_opt cse m
    val check_is = check_initializers_dependencies ctxt deps_opt cse m
    val check_overlap = check_overlap ctxt (SOME e)
    open AstDatatype
    val emp = deps_empty
    fun get_deps f =
      case deps_opt of NONE => emp
      | SOME deps =>
          (case Symtab.lookup deps f of
             SOME x => x
           | NONE => error ("check_expression_dependencies: no variable dependencies for function " ^ f))
    fun insert_global_read x = map_read (map_global_vars (Symuset.insert x))
    fun insert_global_write x = map_write (map_global_vars (Symuset.insert x))

    fun read kind name = if is_global_variable kind then insert_global_read name emp else emp
    fun write kind name = if is_global_variable kind then insert_global_write name emp else emp

    fun right [] = RegionExtras.bogus
      | right [e] = eright e
      | right (_::es) = right es

    fun range [] = (RegionExtras.bogus, RegionExtras.bogus)
      | range [e] = (eleft e, eright e)
      | range (e::es) = (eleft e, right es)

    fun check_args [] = emp
      | check_args (es as (e1::es')) = 
         let 
           val (l, r) = range es
           val d1 = check e1
           val d_es' = check_args es'
         in check_overlap (d1, l) (d_es', r) end       
  in
    case enode e of
      BinOp (bop, e1, e2) => 
        let
          val d1 = check e1
          val d2 = check e2
        in if is_seq_bop bop then deps_union d1 d2 else check_overlap (d1, eleft e1) (d2, eright e2) end
    | UnOp (kind, e1) => (case kind of Addr => check' {mode = Address} e1 | _ => check e1)
    | PostOp (e1, _) => deps_union (check' {mode=LValue} e1) (check e1)
    | PreOp (e1, _) => deps_union (check' {mode=LValue} e1) (check e1)
    | CondExp (e1, e2, e3) => 
       let 
         val d1 = check e1
         val d2 = check e2
         val d3 = check e3
       in deps_unions [d1, d2, d3] end
    | Constant _ => emp
    | Var (name, more_info_ref) =>
       (case !more_info_ref of
         SOME (_, MungedVar {kind, ...}) => 
           (case mode of 
             Address => emp 
           | LValue =>  emp (* sideeffects like ++/-- are only allowed on local variables *)  
           | RValue => read kind name)
       | SOME (_, FunctionName) => get_deps name
       | _ => emp)
    | StructDot (e1, _) => check e1
    | ArrayDeref (e1, e2) => 
        let
          val d1 = check e1
          val d2 = check' {mode = RValue} e2
          val d = check_overlap (d1, eleft e1) (d2, eright e2)
                |> ptr_type (ctype_of e1) ? map_read (map_heap_vars (K true))
        in d end
    | Deref e1 => check e1 |> mode = RValue ? map_read (map_heap_vars (K true))
    | TypeCast (_, e1) => check e1
    | Sizeof e1 => emp
    | SizeofTy _ => emp
    | EFnCall (_, e1, es) => 
        let
          val d1 = check e1
          val d2 = check_args es
        in
          deps_union d1 d2
        end
    | CompLiteral (_, is) => check_is (eleft e) (eright e) is
    | Arbitrary _ => emp
    | MKBOOL e1 => check e1
    | OffsetOf _ => emp
    | AssignE (origin, e1, e2) => 
        let
          val d1 = check' {mode=LValue} e1
          val d2 = check e2
        in check_overlap (d1, eleft e1) (d2, eright e2) end
    | Comma (e1, e2) => 
        let
          val d1 = check e1
          val d2 = check e2
        in deps_union d1 d2 end
    | x => Feedback.error_range ctxt (eleft e) (eright e) ("check_expression_dependencies: unexpected expression:\n " ^  @{make_string} x)
  end
and check_initializer_dependencies ctxt deps cse m i =
  let
    val check = check_expression_dependencies ctxt deps cse m
    open AstDatatype
    val emp = deps_empty
  in
    case i of
      InitE e => check e
    | _ => emp
  end
and check_initializers_dependencies ctxt deps cse m l r is =
  let
    val check_i = check_initializer_dependencies ctxt deps cse m
    open AstDatatype
    val emp = deps_empty
    fun check_list [] = emp
      | check_list (is as (i1::is')) = 
         let 
           val d1 = check_i i1
           val d_is' = check_list is'
         in check_overlap ctxt NONE (d1, l) (d_is', r) end       
  in
    check_list (map snd is)
  end


@{record \<open>datatype local_dependencies = Local_Dependencies of
  {read: Symset.T, write: Symset.T, assign: Symset.T}\<close>};

fun local_dependencies_ord (Local_Dependencies {read = r1, write = w1, assign=a1}, Local_Dependencies {read = r2, write = w2, assign=a2}) =
  prod_ord Symset.ord (prod_ord Symset.ord Symset.ord) 
    ((r1, (w1, a1)), (r2, (w2, a2)))

val lempty = Local_Dependencies {read = Symset.empty, write = Symset.empty, assign = Symset.empty}

fun ldeps_union
  (Local_Dependencies {read = r1, write = w1, assign = a1}) (Local_Dependencies {read = r2, write = w2, assign=a2}) =
  Local_Dependencies {read = Symset.union r1 r2, 
    write = Symset.union w1 w2 , assign = Symset.union a1 a2}

fun ldeps_inter
  (Local_Dependencies {read = r1, write = w1, assign = a1}) (Local_Dependencies {read = r2, write = w2, assign = a2}) =
  Local_Dependencies {read = Symset.inter r1 r2, 
    write = Symset.inter w1 w2, assign = Symset.inter a1 a2}

fun ldeps_unions [] = lempty
  | ldeps_unions (x::xs) = ldeps_union x (ldeps_unions xs)

fun assign_to_write (Local_Dependencies {read, write, assign}) =
  (Local_Dependencies {read=read, write = Symset.union write assign, assign=Symset.empty})

fun check_local_var ctxt e =
  let
    fun err () = Feedback.error_range ctxt (eleft e) (eright e) ("expecting local variable")
  in
    case enode e of
      Var (name, more_info_ref) =>
         (case !more_info_ref of
           SOME (_, MungedVar {kind, ...}) => 
             if is_global_variable kind then err () else name
          | _ => err ())
    | _ => err ()
  end


fun check_locals_overlap ctxt (e_opt: expr option) (d1, l) (d2, r) =
  let
    fun err msg vars = Feedback.error_range ctxt l r 
      ("overlapping " ^ msg ^ " in expression:\n " ^ @{make_string} vars ^ 
        "\n d1: " ^ @{make_string} d1 ^
        "\n d2: " ^ @{make_string} d2 ^ 
        (case e_opt of SOME e => "\n e: "  ^ @{make_string} e | _ => ""))
    val inter_writes = Symset.inter (get_write d1) (get_write d2)
    val _ = Symset.is_empty inter_writes orelse err "writes-writes" inter_writes
    val inter_writes_reads = Symset.inter (get_write d1) (get_read d2)
    val _ = Symset.is_empty inter_writes_reads orelse err "writes-reads" inter_writes_reads
    val inter_reads_writes = Symset.inter (get_read d1) (get_write d2)
    val _ = Symset.is_empty inter_reads_writes orelse err "reads-writes" inter_reads_writes
  in
    ldeps_union d1 d2
  end

fun check_assign_overlap ctxt (e_opt: expr option) origin (d1, l) (d2, r) =
  let
    fun err msg vars = Feedback.error_range ctxt l r 
      ("overlapping " ^ msg ^ " in expression:\n " ^ @{make_string} vars ^ 
        "\n d1: " ^ @{make_string} d1 ^
        "\n d2: " ^ @{make_string} d2 ^ 
        (case e_opt of SOME e => "\n e: "  ^ @{make_string} e | _ => ""))
    val d = check_locals_overlap ctxt e_opt (d1, l) (d2, r)
    val inter_assign_writes = Symset.inter (get_assign d1) (get_write d2)
    val _ = Symset.is_empty inter_assign_writes orelse err "assign-writes" inter_assign_writes
  in
    case origin of AstDatatype.Expression => assign_to_write d | AstDatatype.Statement => d
  end

fun check_expression_sideeffects ctxt (m as {mode:mode}) e =
  let

    val check' = check_expression_sideeffects ctxt
    val check = check' m

    val check_is = check_initializers_sideeffects ctxt m

    val check_overlap = check_locals_overlap ctxt (SOME e)
    val check_assign_overlap = check_assign_overlap ctxt (SOME e)

    fun insert_read name = map_read (Symset.insert name)
    fun insert_write name = map_write (Symset.insert name)
    fun insert_assign name = map_assign (Symset.insert name)

    fun read name = insert_read name lempty
    fun write name = insert_write name lempty
    fun assign name = insert_assign name lempty

    fun right [] = RegionExtras.bogus
      | right [e] = eright e
      | right (_::es) = right es

    fun range [] = (RegionExtras.bogus, RegionExtras.bogus)
      | range [e] = (eleft e, eright e)
      | range (e::es) = (eleft e, right es)

    fun check_args [] = lempty
      | check_args (es as (e1::es')) = 
         let 
           val (l, r) = range es
           val d1 = check e1
           val d_es' = check_args es'
         in check_overlap (d1, l) (d_es', r) end

  in
    case enode e of
      BinOp (bop, e1, e2) => 
        let
          val d1 = check e1
          val d2 = check e2
        in if is_seq_bop bop then ldeps_union d1 d2 else check_overlap (d1, eleft e1) (d2, eright e2) end
    | UnOp (kind, e1) => (case kind of Addr => check' {mode = Address} e1 | _ => check e1)
    | PostOp (e1, _) => 
        let val x = check_local_var ctxt e1 in insert_write x (read x) end
    | PreOp (e1, _) => 
        let val x = check_local_var ctxt e1 in insert_write x (read x) end
    | AssignE (origin, e1, e2) => 
        let
          val d1 = check' {mode=LValue} e1
          val d2 = check' {mode=RValue} e2
        in check_assign_overlap origin (d1, eleft e1) (d2, eright e2) end
    | CondExp (e1, e2, e3) => 
       let 
         val d1 = check e1
         val d2 = check e2
         val d3 = check e3
       in ldeps_unions [d1, d2, d3] end
    | Constant _ => lempty
    | Var (name, more_info_ref) =>
       (case !more_info_ref of
         SOME (_, MungedVar {kind, ...}) => 
           (case mode of 
             Address => lempty 
           | LValue =>  if is_global_variable kind then lempty else assign name
           | RValue => if is_global_variable kind then lempty else read name)
       | _ => lempty)
    | StructDot (e1, _) => check e1
    | ArrayDeref (e1, e2) => 
        let
          val d1 = check e1
          val d2 = check' {mode = RValue} e2
          val d = check_overlap (d1, eleft e1) (d2, eright e2)
        in d end
    | Deref e1 => check e1
    | TypeCast (_, e1) => check e1
    | Sizeof e1 => lempty
    | SizeofTy _ => lempty
    | EFnCall (_, e1, es) => 
        let
          val d1 = check e1
          val d2 = check_args es
        in
          lempty
        end
    | CompLiteral (_, is) => check_is (eleft e) (eright e) is
    | Arbitrary _ => lempty
    | MKBOOL e1 => check e1
    | OffsetOf _ => lempty
    | Comma (e1, e2) => 
        let
          val d1 = check e1
          val d2 = check e2
        in ldeps_union d1 d2 end
    | x => Feedback.error_range ctxt (eleft e) (eright e) ("check_expression_sideffects: unexpected expression:\n " ^  @{make_string} x)
  end
and check_initializer_sideeffects ctxt m i =
  let
    val check = check_expression_sideeffects ctxt m

  in
    case i of
      InitE e => check e
    | _ => lempty
  end
and check_initializers_sideeffects ctxt m l r is =
  let
    val check_i = check_initializer_sideeffects ctxt m
    fun check_list [] = lempty
      | check_list (is as (i1::is')) = 
         let 
           val d1 = check_i i1
           val d_is' = check_list is'
         in check_locals_overlap ctxt NONE (d1, l) (d_is', r) end       
  in
    check_list (map snd is)
  end

fun get_var_info cse fname_opt n =
  let
    val vars = get_vars cse
    val occurs = these (Symtab.lookup vars n)
    val matches = filter (fn x => get_fname x = fname_opt) occurs
  in
    case matches of 
     (info::_) => info
    | [] => error ("get_var_info: no entry for " ^ @{make_string} (fname_opt, n))
  end

val is_addressed = XMSymTab.defined o get_addressed

fun is_addressed_var cse fname_opt n =
  let
    val info = get_var_info cse fname_opt n
  in
    is_addressed cse (get_mname info, fname_opt)
  end

(* fname is a string option : NONE corresponds to a declaration at the global
   level *)
fun process_decl ctxt fname {open_block} (d:declaration wrap) (e as Csenv {senv,...}) = let
  val ecenv = cse2ecenv ctxt e
  fun puredecl d = {decls = [d], localinits = [], globalinits = [], pop = I}
  fun pex e env = fst (process_expr ctxt RV fname [] env e)
  fun pex' e env = process_expr ctxt RV fname [] env e
  fun pexs exps e = (e, Binaryset.empty expr_ord)  
    |> fold (fn exp => fn (e, s1) => let val (e', s2) = pex' exp e in (e', Binaryset.union (s1, s2)) end) exps
  val pst = process_stmt ctxt (the_default "" fname) []
  fun pstmts e stmts = 
    let
      val (stmtss, e') = fold_pipe pst e stmts
    in (flat stmtss, e') end
  fun pbil block_info e blist = process_blockitems ctxt (fname_str fname) block_info e blist
in
  case node d of
    VarDecl (ty,s,storage_specs,iopt,attrs) => let
      val calls_attrs = filter is_calls_attr attrs
      fun calls_attrs_stmt s = if null calls_attrs then s else
        let
          val x = snode s
          val l = sleft s
          val r = sright s
        in
          swrap (AttributeStmt (wrap (calls_attrs, l, r), s), l, r)
        end
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
      val (vi, e) = if open_block then (vi, e) else insert_var ctxt (vi, e)
      (* inserting vi may force further munging if the name is already being
         used at a different type *)
      val munged_name = get_mname vi
      val bogus = SourcePos.bogus
      val mvinfo = MungedVar {munge = munged_name,
                              owned_by = StmtDecl.get_owned_by attrs, fname=fname, init=true, 
                              kind = the_variable_info e vi}
      val var_e = ewrap(Var (str, Unsynchronized.ref (SOME (vty, mvinfo))), left s, right s)
      val d' = wrap(VarDecl(ty,s,storage_specs,NONE,attrs), left d, right d)
      val (decls, inits, proc_expr_opt, e, pop) =
          (case iopt of
            NONE => let
            in
              case fname of
                NONE => ([d'], [], NONE, e, I)
              | SOME _ => ([], [swrap(LocalInit var_e, left s, right s)],
                           NONE,
                           e, I)
            end
          | SOME (InitE exp0) => let
              val (bl, exp) = dest_statement_expression ctxt exp0
              val e = new_scope e
              val (bl', e) = pbil {open_block=false} e bl
              fun w s0 = swrap (s0, left s, eright exp)
            in
              (case enode exp of
                EFnCall(origin, e_fn,args) => let
                  val called =
                      case (enode e_fn, cse_typing {report_error=true} ctxt e e_fn) of
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
                          FnPtrCall (fty, approx_expr ctxt e (enode e_fn), is_some (dest_method_fun_ptr (fname_str fname) {report_error=true} ctxt [] e e_fn))
                        end
                  val e = new_call ctxt {caller = fname_str fname, callee = called, args=args} e
                  val () = case fname of
                            NONE =>
                              eFail ctxt (exp, "Can't initialise a global with a \
                                                \function call")
                          | SOME _ => ()
                in
                  ([], wrap_block (eleft exp0) (eright exp0) bl' [w (AssignFnCall(SOME var_e, e_fn, args))],
                   SOME exp,
                   e, pop_scope)
                end
              | _ => let
                  val e = case fname of
                            NONE => map_globinits (MSymTab.update (munged_name, exp)) e
                          | _ => e
                in
                  ([], wrap_block (eleft exp0) (eright exp0) bl' [w (Assign(var_e, exp))], SOME exp, e, pop_scope)
                end)
            end
          | SOME (InitList ilist) => let
              fun w s0 = swrap (s0, left s, right s)
              val exp = ewrap(CompLiteral(ty, ilist), right s, right d)
              val e =
                  case fname of
                    NONE => map_globinits (MSymTab.update (munged_name, exp)) e
                  | _ => e
            in
              ([], [w (Assign(var_e, exp))], SOME exp, e, I)
            end)
      val e =
          case proc_expr_opt of
              NONE => e
            | SOME exp => 
                if is_none fname then pex exp e (* global expressions are checked here *)
                else e (* expression appears as subexpression in 
                          localinits and thus is processed in statement *) 
                         
      val (globalinits, localinits) =
          case fname of
              NONE => (inits, [])
            | SOME _ => ([], inits)
      val localinits' = map calls_attrs_stmt localinits
    in
      ({decls = decls, localinits = localinits', globalinits = globalinits, pop = pop}, e)
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
and process_blockitem ctxt fname block_info e bi = let
in
  case bi of
    BI_Stmt s => apfst (map BI_Stmt) (process_stmt ctxt fname [] e s)
  | BI_Decl d =>
    let
      val ({decls,localinits,globalinits, pop}, e') = process_decl ctxt (SOME fname) block_info d e
      (* process the new local inits in the process_stmt sense.
         [] already did most of the work, but this is the best
         opportunity to treat problematic function calls as embedded
         (see treat_as_emb_fcall) *)
      val (stmts, e'') = fold_pipe (process_stmt ctxt fname []) e' localinits
    in
      (* throw away globalinits for the moment *)
      (map BI_Decl decls @ map BI_Stmt (List.concat stmts), pop e'')
    end
end
and process_stmt ctxt fname attrss e (stmt : statement) = let
  fun pex' e exp = process_expr ctxt RV (SOME fname) attrss e exp
  fun pex e exp = 
    let 
      val (e1, grs) = pex' e exp
      val _ = check_expression_sideeffects ctxt {mode=RValue} exp
    in (e1, grs) end
  fun pexs e exps = (e, Binaryset.empty expr_ord)  
    |> fold (fn exp => fn (e, s1) => let val (e', s2) = pex e exp in (e', Binaryset.union (s1, s2)) end) exps
  fun pattr (GCC_AttribFn (x, es)) e = (e |> fold (fn exp => fn e => pex e exp |> fst) es)
    | pattr _ e = e
  fun pexlv e exp = process_expr ctxt LV (SOME fname) attrss e exp
  val pst_attrs = process_stmt ctxt fname
  fun pst e st = pst_attrs attrss e st
  fun pstmts e stmts = 
    let
      val (stmtss, e') = fold_pipe pst e stmts
    in (flat stmtss, e') end
  fun pbil open_block e blist = process_blockitems ctxt fname open_block e blist


  fun w s0 = swrap(s0, sleft stmt, sright stmt)
  val retty = get_rettype fname e
  fun lift_stmts stmts =
      case stmts of
          [] => w EmptyStmt
        | [s] => s
        | _ => w(Block (AstDatatype.Closed, map BI_Stmt stmts))
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
    While(g0, i, s) => let
      val (bl, g) = dest_statement_expression ctxt g0
      val e = new_scope e
      val (bl', e) = pbil {open_block=false} e bl
      val stmts' = if null bl' then [] else [swrap (Block (AstDatatype.Open, bl'), sleft stmt, eleft g)] 
      val (e,grs) = pex e g
      val _ = check_expression_sideeffects ctxt {mode=RValue} g 
      val cstmts = mk_chaos_stmts grs    
      val (s', e) = pst e s  
    in
      (wrap_block (sleft stmt) (sright stmt) bl' (cstmts @ [w (While(g,i,lift_stmts (s' @ stmts' @ cstmts)))]), pop_scope e)
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
  | IfStmt(g0,s1,s2) => let
      val (bl, g) = dest_statement_expression ctxt g0
      val e = new_scope e
      val (bl', e) = pbil {open_block=false} e bl
      val (e, grs) = pex e g
      val (s1',e) = pst e s1
      val (s2',e) = pst e s2
    in
      (wrap_block (sleft stmt) (sright stmt) bl' ( prechaos grs [w (IfStmt(g,lift_stmts s1',lift_stmts s2'))]), pop_scope e)
    end
  | Block (kind, b) =>
      let
        val (new_scope, pop_scope, open_block) = 
          case kind of 
            AstDatatype.Closed => (new_scope, pop_scope, false) 
          | AstDatatype.Open => (I, I, true)
      in 
        apfst (single o w o (fn bl => Block (kind, bl))) (apsnd pop_scope (pbil {open_block=open_block} (new_scope e) b))
      end
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
      val _ = map (check_nested_switch ctxt o snd) cases
      val (e, grs) = apfst new_scope (pex e g)
      fun label_fold NONE env = env
        | label_fold (SOME exp) env = #1 (pex env exp)
            (* should be no global reads in a case label *)
      fun one_case e (eoptlist, bis) = let
        val e = e |> fold label_fold eoptlist
      in
        apfst (fn y => (eoptlist,y)) (pbil {open_block=false} e bis)
      end
    in
      apfst (fn cs => prechaos grs [w (Switch(g,cs))])
            (apsnd pop_scope (fold_pipe one_case e cases))
    end
  | Assign(expr1,expr2_initial) =>
     let
       val (bl, expr2) = dest_statement_expression ctxt expr2_initial
       val e = new_scope e
       val (bl', e) = pbil {open_block=false} e bl
       val assignE = (ewrap (AssignE (AstDatatype.Statement, expr1, expr2), sleft stmt, sright stmt))
       val (e, grs) = pex e assignE
       val _ = check_expression_sideeffects ctxt {mode=RValue} assignE
       val stmt' = w (Assign(expr1, expr2))

       val modified = get_modified ctxt e expr1
       val e =
           case modified of
             NONE => e
           | SOME m => add_modification fname m e
       val e1 = 
         if CType.fun_ptr_type (cse_typing {report_error=true} ctxt e expr1) then
           let
             val xs = approx_expr ctxt e (enode expr1)
             val object_ts = map_filter approx_ctyp xs |> filter_out (fn (_, selectors) => null selectors)
             val vs = approx_expr ctxt e (enode expr2)
             val fs = vs |> filter (null o #3) |> map #1             
           in case (object_ts, fs) of 
             ([(ctyp, selectors)], [fname]) => add_method_approx (ctyp, selectors) fname e 
             | _ => e end
         else e
     in
       (wrap_block (sleft stmt) (sright stmt) bl' (prechaos grs [stmt']), pop_scope e1)
     end
  
  | AssignFnCall(eopt,fn_e,args) => let 
      in     
      if treat_as_emb_fcall ctxt fname attrss e (eopt,fn_e,args)
      then let
        val lv = case eopt of SOME lv => lv
          | NONE => raise Fail "Trying to embed fcall without lval."
      in pst e (w (Assign(lv,ebogwrap (EFnCall(AstDatatype.Statement, fn_e,args))))) end
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
        (* val (e,grs2) = pexs e (fn_e::args) *)
        val (e,grs2) = pex e (ebogwrap (EFnCall(AstDatatype.Statement, fn_e,args)))
        val grs = Binaryset.union(grs1,grs2)
        val (callee, _) = fndes_callinfo ctxt fname attrss e fn_e
        (* the arguments need to be considered as being part of one big
           expression (rather than independently) in order for the
           embedded function call analysis to work, so we create one fake
           expression embodying them all to be analysed by pex *)
        val e = new_call ctxt {caller = fname, callee = callee, args = args} e
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
  | Return (SOME ex0) => let
      val (bl, ex) = dest_statement_expression ctxt ex0
      val e = new_scope e
      val (bl', e) = pbil {open_block=false} e bl
      val stmt' = w (Return (SOME ex))
    in
      case retty of
        NONE => raise stmt_fail (stmt, "Returning a value in a void function")
      | SOME ty => let
          val etyp = cse_typing {report_error=true} ctxt e ex
        in
          if ExpressionTyping.assignment_compatible (ty, etyp, ex) then
            let
              val (e,grs) = pex e ex
            in
              (wrap_block (sleft stmt) (sright stmt) bl' (prechaos grs [stmt']), pop_scope e)
            end
          else
            raise stmt_fail (stmt,
                             "Type of returned expression ("^tyname etyp^
                             ") incompatible with that of containing function ("^
                             tyname ty^")")
        end
    end
  | ReturnFnCall(fn_e, args) => let in
      if treat_ret_as_emb_fcall ctxt fname attrss e (retty,fn_e,args)
      then pst e (w (Return (SOME (ebogwrap (EFnCall(AstDatatype.Statement, fn_e,args))))))
      else let
        val (e,grs) = pex e (ebogwrap (EFnCall(AstDatatype.Statement, fn_e,args)))
        val (callee, _) = fndes_callinfo ctxt fname attrss e fn_e
        val e = new_call ctxt {caller = fname, callee = callee, args = args} e
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
  | AttributeStmt(attrs, s) => let
      val e1 = fold pattr (node attrs) e
      val (s', e2) = pst_attrs (attrs::attrss) e1 s
    in
      ([w (AttributeStmt(attrs, lift_stmts s'))], e2)
    end
  | _ => ([stmt], e)
end
and process_blockitems ctxt (fname : string) block_info (env : csenv) bis =
    apfst List.concat (fold_pipe (process_blockitem ctxt fname block_info) env bis)

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
  let
  in
    case edec of
      Decl d => let
        val ({decls, localinits, globalinits, pop}, e) = process_decl ctxt NONE {open_block=false} d env0
      in
        ((map Decl decls, globalinits), pop e)
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
        val (body0, env) = process_blockitems ctxt (node s) {open_block=false} env (node body)
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
  end

fun truncate_ptr (Ptr cty) = cty
  | truncate_ptr cty = cty


fun method_approx_callees_raw cse x = 
  case CTypeSelectorsTab.lookup (get_method_approx cse) x of 
    SOME X => Binaryset.listItems X
  | _ => []

val int_ctype_ord = ctype_ord int_ord I
val eq_int_ctype = is_equal o int_ctype_ord 

fun get_paths (senv: senv) (from: int ctype) (to: int ctype) : selector list list =
  let
    fun get_paths_field (fld, (fldTy, _)) = get_paths senv fldTy to |> map (cons (Field (node fld)))
  in
    if eq_int_ctype (from, to) then [[]]
    else 
      (case from of
        Array (elTy, _) => get_paths senv elTy to |> (map (cons (Index NONE)))
      | StructTy s => 
          (case AList.lookup (op =) senv s of
            SOME (_, flds, _, _) => maps get_paths_field flds
          | _ => []) 
      | _ => [])
  end

fun match_access (Field x) (Field y) = x = y
  | match_access (Index (SOME x)) (Index (SOME y)) = x = y
  | match_access (Index _) (Index _) = true
  | match_access _ _ = false

fun match_accesses xs ys = length xs = length ys andalso forall (uncurry match_access) (xs ~~ ys)

fun approx_global_fun_ptrs_from_ty cse (ty, selectors) =
  let 
    val senv = get_senv cse
    val global_approx = approx_globals' cse
    val global_vars = get_variables cse NONE
    fun get_info n = find_first (fn v => srcname v = n) global_vars
    fun approx_ty (n, xs) = 
      case get_info n of NONE => []
      | SOME info => 
         let
           val paths = get_paths senv (get_vtype info) ty
           val full_paths = map (fn xs => xs @ selectors) paths
           val matches = map_filter (fn (ps, ys) => if exists (match_accesses ps) full_paths then SOME (map fst ys) else NONE) xs
         in 
           flat matches 
         end
    val all_matches = maps approx_ty global_approx |> sort_distinct fast_string_ord
  in 
    all_matches
  end

fun method_approx_callees cse x
  = method_approx_callees_raw cse x @ approx_global_fun_ptrs_from_ty cse x
fun approx_callees cse (name, var_info, selectors) =
  case !var_info of
    NONE => []
  | SOME (_, FunctionName) => [name] (* direct function name from global dispatcher variable *)
  | SOME (cty, MungedVar {kind, fname = SOME name, ...}) => 
      (case kind of 
        Parameter i => 
           let
           in 
             if null selectors then 
               get_fun_ptr_param_callees cse name i 
             else 
               method_approx_callees cse (truncate_ptr cty, selectors) end
       | _ => 
             method_approx_callees cse (truncate_ptr cty, selectors)) 
  | _ => []

and get_fun_ptr_param_callees cse fname param =
  case Symtab.lookup (get_fun_ptr_params cse) fname of
    SOME xs => 
     let
     in
      (case try (nth xs) param of 
        SOME (SOME vs) => maps (approx_callees cse) vs 
       | _ => [])
     end
  | _ => []

fun gen_compute_callgraphs excludes env = let
  fun add fname s = if member (op =) excludes fname then s else Binaryset.add(s, fname)

  val (callgraph, converse) = let
    fun setfoldthis caller (fncall, acc) =
        case fncall of
          DirectCall nm => add nm acc
        | FnPtrCall (fty, potential_callees,_) =>
           let
             val fun_ptr_callees = potential_callees |> maps (approx_callees env)  
           in
             Binaryset.addList(acc, fun_ptr_callees)
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

fun mvar_traverse env = let
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
  val {callees,callers} = compute_callgraphs env

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
    fun mk_set ts = Binaryset.addList (Binaryset.empty (ctype_ord int_ord I), ts)
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
          SOME (Union active, flds, _, _) => map (#1 o #2) (CType.active_variants s active flds)
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
    fun is_fun (n, r, _) = case !r of SOME (_, FunctionName) => SOME n | _ => NONE
  in
    get_fun_ptr_params cse |> Symtab.dest
    |> map (map_filter (is_fun) o flat o map_filter I o snd)
    |> flat |> distinct (op =)
  end

fun has_fun_ptr_params_called_with_object_method cse =
  let
    fun is_method (n, r, []) = false
      | is_method (n, r, xs) = true
  in
    get_fun_ptr_params cse |> Symtab.dest |> map snd |> flat |> maps these |> exists is_method
  end

fun method_callers_via_fun_ptr_param cse =
  let
    fun method_caller (n, r, []) = NONE
      | method_caller (n, r, xs) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname, ...}) => SOME fname 
         | _ => NONE )
  in
    get_fun_ptr_params cse |> Symtab.dest |> map snd |> flat |> maps these 
    |> map_filter method_caller |> sort_distinct fast_string_ord
  end

fun callers_via_fun_ptr_param cse =
  let
    fun caller (n, r, _) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname, ...}) => SOME fname 
         | _ => NONE )
  in
    get_fun_ptr_params cse |> Symtab.dest |> map snd |> flat |> maps these 
    |> map_filter caller |> sort_distinct fast_string_ord
  end

fun callers_via_local_fun_ptr_param cse =
  let
    fun caller (n, r, _) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname, kind=Local, ...}) => SOME fname 
         | _ => NONE )
  in
    get_fun_ptr_params cse |> Symtab.dest |> map snd |> flat |> maps these 
    |> map_filter caller |> sort_distinct fast_string_ord
  end

fun method_callers_via_fun_ptr_param_of cse fname =
  let
    fun method_caller (n, r, []) = NONE
      | method_caller (n, r, xs) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname', ...}) => SOME fname' 
         | _ => NONE )
  in
    Symtab.lookup (get_fun_ptr_params cse) fname |> these |> map_filter I |> flat 
    |> map_filter method_caller     
    |> sort_distinct fast_string_ord
  end

fun callers_via_fun_ptr_param_of cse fname =
  let
    fun caller (n, r, _) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname', ...}) => SOME fname' 
         | _ => NONE )
  in
    Symtab.lookup (get_fun_ptr_params cse) fname |> these |> map_filter I |> flat 
    |> map_filter caller     
    |> sort_distinct fast_string_ord
  end

fun callers_via_method_or_non_param_of_fun_ptr_param_of cse fname =
  let
    fun non_param_caller (n, r, xs) = 
         (case !r of 
           SOME (_, MungedVar {fname = SOME fname', munge, ...}) => 
             if null xs then
               (case get_local_info cse (munge, SOME fname') of 
                  SOME {kind, ...} => 
                  (case kind of NameGeneration.In _ =>  NONE | _ => SOME fname') 
                  | _ => SOME fname')
             else
                SOME fname'
         | _ => NONE )
  in
    Symtab.lookup (get_fun_ptr_params cse) fname |> these |> map_filter I |> flat 
    |> map_filter non_param_caller     
    |> sort_distinct fast_string_ord
  end

local

fun is_non_proto cse name =
  case (Symtab.lookup (get_fninfo cse) name |> Option.map #2) of
    NONE => false
  | SOME is_proto => not is_proto
in
fun get_referenced_funs_global cse =
   these (Symtab.lookup (get_referenced_funs cse) "") |> filter (is_non_proto cse)

fun get_all_referenced_funs {with_proto} cse =
   (Symtab.dest (get_referenced_funs cse) ) |> map snd |> flat |> distinct (op =) |> filter (if with_proto then (K true) else is_non_proto cse)

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
    get_functions_used_as_fun_ptr_params cse @ glob_fun_ptr |> sort_distinct (fast_string_ord)
  end
end

fun mk_fun_ty (retT, _, vinfos) = Function (retT, map get_vtype vinfos)
fun get_global_fun_ptrs_grouped_by_type cse  =
   let
     val fninfo = get_fninfo cse
     fun get_cty f = Symtab.lookup fninfo f |> Option.map mk_fun_ty |> the
     val fun_ptr_funs = get_functions_used_via_fun_ptr cse
     val res = get_constant_global_fun_ptrs cse |> map snd |> flat
     |> filter (member (op =) fun_ptr_funs)
     |> sort_distinct fast_string_ord
     |> map (fn x => (x, get_cty x))
     |> Utils.buckets (fn ((_, cty1), (_, cty2)) => cty1 = cty2)
   in
     res
   end

fun get_fun_ty cse fname = Symtab.lookup (get_fninfo cse) fname |> Option.map mk_fun_ty

fun get_global_fun_ptr_group_with_same_type cse fname =
 case get_fun_ty cse fname  of
   SOME cty =>
   let
     val fninfo = get_fninfo cse
     fun get_cty f = Symtab.lookup fninfo f |> Option.map mk_fun_ty |> the
     val fun_ptr_funs = get_functions_used_via_fun_ptr cse
     val globs = get_constant_global_fun_ptrs cse |> map snd 
     |> filter (fn xs => member (op =) xs fname) |> flat
     |> filter (member (op =) fun_ptr_funs)
     |> filter (fn f => get_cty f = cty)
    val res = fname :: globs |> sort_distinct fast_string_ord
   in
     res
   end
 | NONE => [fname]

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
    [(adglob_rcd_tyname, (Struct, map (fn vi => (RegionExtras.bogwrap (srcname vi), (get_vtype vi, []))) advis, Region.bogus, []))]
end


fun callers_with_addressable_variables cse fname =
  let
    val callers = get_final_callers cse [fname]
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
                   Feedback.error_region ctxt reg ("union " ^ quote nm ^ " has a non-packed variant: " ^ quote (node fld_name) ^ 
                     ":\n " ^ str)
              end
         in
         (if length active > 1 andalso Binaryset.member (usedtypes, UnionTy nm) then
            (* First active variant is considered to be the canonical type representing the union;
             * It gets the same name as the union and thus "overrides" the entry for the union when preparing
             * all records for the 'recursive record package' definitions, cf. Calculate_State.get_sorted_structs *)
            [(nm, map_index (fn (i, (variant_name, fld as (ty, _))) => 
                            let val _ = check variant_name ty
                            in (node variant_name, [(nm ^ (if i = 0 then "" else  "'" ^ (node variant_name)), (Struct, [(variant_name, fld)], reg, align_attr::attrs))]) end) 
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
            map (fn (fld_name, fld) => (nm ^ "'" ^ (node fld_name), (Struct, [(fld_name, fld)], reg, attrs))) flds 
          else []) @ 
         [entry]
    val senv' = maps expand senv
  in
    senv'
  end
fun process_decls ctxt cfg (p : program) = let
  fun recurse (ds, is) (env, edecs) =
    let
    in
      case edecs of
        [] => ((List.rev ds, List.rev is), env)
      | e :: es => let
          val ((ds0, is0), env') = process_one_extdecl ctxt env e
        in
          recurse (List.revAppend(ds0,ds), List.revAppend(is0, is)) (env', es)
        end
    end
  val init_cse = emptycse cfg |> add_exit
  val (i, env) = recurse ([], []) (init_cse, p)
  fun check (rcd as (name, (kind, flds, r, attrs))) =
    let
       val _ = gen_sizeof false false env (type_of_rcd rcd)
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
  val env = mvar_finalise (mvar_traverse env)
  val env = map_read_globals (K orig_read_globals) env
  val env = map_fun_ptr_params (compress_fun_ptr_params) env
  val env = map_constant_global_fun_ptrs (K (approx_global_fun_ptrs env)) env


  val all_addressed_funs = get_all_addressed_funs env
  val all_referenced_funs = get_all_referenced_funs {with_proto=true} env
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
    sort_strings (List.map render_mungedb_line info)

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
      val data = sort_strings data0
    in List.app (fn s => File_Stream.output outstrm (s ^ "\n")) data end)

fun is_reachable (callee_graph: string Binaryset.set Symtab.table) caller callee =
  let
    fun immediate_callees caller = 
      case Symtab.lookup callee_graph caller of 
       SOME X => X
      | NONE => Binaryset.empty (String.compare)

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
    reach (Binaryset.empty String.compare) caller
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

fun get_functions_with_sig cse (retT, argTs) =
  Symtab.dest (get_fninfo cse)
  |> map_filter (fn (n, (retT',is_proto,args)) => 
    if not is_proto andalso norm_enum retT' = retT andalso map (norm_enum o get_vtype) args = argTs then SOME n else NONE)

fun potential_method_callees cse =
  let
    val sigs = method_types cse
  in maps (get_functions_with_sig cse) sigs |> sort_distinct (fast_string_ord) end


fun get_fun_ptr_clique cse =
  let
    val core = get_fun_ptr_core_clique cse
    val extended = 
      if null core then [] else
         the_default core (get_clique cse (hd core))
  in
    extended
  end

fun get_fun_ptr_clique_fun_ptrs cse =
  let
    val fun_ptr_funs = get_functions_used_via_fun_ptr cse
    val fun_ptr_recursion_clique = get_fun_ptr_clique cse
  in 
    fun_ptr_recursion_clique
    |> filter (member (op =) fun_ptr_funs)
  end


fun check_expression_dependencies' ctxt deps cse (fname, e) =
  let
    val global_deps = check_expression_dependencies ctxt (SOME deps) cse {mode=RValue} e
    val local_deps = check_expression_sideeffects ctxt {mode=RValue} e
    val addressed_locals = Symset.union (get_write local_deps) (get_read local_deps) 
      |> Symset.dest |> filter (is_addressed_var cse (SOME fname))
    val read_heap = AstDatatype.get_heap_vars (AstDatatype.get_read global_deps)
    val write_heap = AstDatatype.get_heap_vars (AstDatatype.get_write global_deps)
    val _ = null addressed_locals 
      orelse (AstDatatype.bool_is_empty read_heap andalso AstDatatype.bool_is_empty write_heap) 
      orelse Feedback.error_range ctxt (eleft e) (eright e)
        ("function calls and addressed local variables may not be mixed in an expression:\n " ^ @{make_string} addressed_locals ^ 
          "\n " ^ @{make_string} (fname, e))
  in
    global_deps
  end

fun check_embedded_fncall_exprs ctxt cse =
  let
    val cliques = get_cliques cse
    val relevant_functions = Symset.make (flat cliques)
    val embedded_fncall_exprs' = get_embedded_fncall_exprs cse
      |> Symtab.dest |> filter (Symset.member relevant_functions o fst) |> maps (fn (x, vs) => map (pair x o fst) vs)

    val embedded_fncall_exprs = get_embedded_fncall_exprs cse
      |> Symtab.dest |> filter (Symset.member relevant_functions o fst) |> maps snd |> map fst
    val n = length embedded_fncall_exprs
    val deps = get_variable_dependencies cse
    fun pmap f = if Config.get ctxt single_threaded then map f else Par_List.map f
(*
    val _ = Utils.timeit_label 2 ctxt ("check_embedded_fncall_exprs (" ^ string_of_int n ^ ")") (fn _ => 
      pmap (check_expression_dependencies ctxt (SOME deps) cse {mode=RValue}) (embedded_fncall_exprs))
*)
    val _ = Utils.timeit_label 2 ctxt ("check_embedded_fncall_exprs (" ^ string_of_int n ^ ")") (fn _ => 
      pmap (check_expression_dependencies' ctxt deps cse) (embedded_fncall_exprs'))
  in
    ()
  end 

fun map_assign_lhs f (AstDatatype.Assign (e1, e2)) = AstDatatype.Assign (f e1, e2)
  | map_assign_lhs f x = x

fun make_init_globals_function constant_globals init_stmts =
  let
    open AstDatatype Expr RegionExtras StmtDecl
    fun relevant_assignment s =
      (case snode s of
         Assign (e1, _) => 
           (case enode e1 of 
             Var (_, more_info_ref) =>
               (case !more_info_ref of
                  SOME (_, MungedVar {munge, ...}) => if MSymTab.defined constant_globals munge then NONE else SOME s
                | _ => NONE)
           | _ => NONE) 
      | _ => NONE)
    val relevant_inits = map_filter relevant_assignment init_stmts
    val relevant_inits' = 
      map ((map_snode o map_assign_lhs o map_enode o map_var o apsnd o AstDatatype.map_more_info o map_munged_var o map_init)
             (K false)) 
      relevant_inits
    val fn_def = FnDefn ((CType.Void, wrap (NameGeneration.init_globalsN, bogus, bogus)), [], [], (wrap (map BI_Stmt relevant_inits', bogus, bogus)))

  in
    fn_def
  end

fun add_init_globals_fun init_stmts cse =
  let
    val all_constant_globals = get_untouched_globals cse
    val init_globals_def = make_init_globals_function all_constant_globals init_stmts
    val cse' = cse 
      |> update_hpfninfo init_globals_def
      |> map_fninfo (Symtab.update (NameGeneration.init_globalsN, (Void, false, [])))
  in cse' end

fun variant_origin cse name =
 let
   val union_variants = get_union_variants cse
 in
   find_first (fn (_, vs) => (exists (fn (_, xs) => exists (fn (n, _) => n = name) xs) vs)) union_variants |> Option.map #1
 end

fun contains_packed_attr (senv: senv) ty =
  let
    fun contains_packed s = 
      case AList.lookup (op =) senv s of NONE => 
        error ("contains_packed_type: unknown type: " ^ s)
      | SOME (_, flds, _, attrs) => 
          exists is_packed_attr attrs orelse exists (contains_packed_attr senv) (map (#1 o #2) flds)   
  in
    case ty of
      StructTy s => contains_packed s
    | UnionTy u => contains_packed u
    | Array (eT, _) => contains_packed_attr senv eT
    | _ => false
  end
end (* struct *)

(* Local variables: *)
(* mode: sml *)
(* End: *)
