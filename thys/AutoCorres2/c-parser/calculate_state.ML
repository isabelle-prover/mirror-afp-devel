(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature CALCULATE_STATE =
sig

  val generate_umm_types_file : bool Config.T

  type var_info = ProgramAnalysis.var_info
  type csenv = ProgramAnalysis.csenv
  type 'a ctype = 'a Absyn.ctype
  type ecenv = Absyn.ecenv
  type 'a rcd_env = 'a ProgramAnalysis.rcd_env
  type nm_info = ProgramAnalysis.nm_info

  val define_enum_consts : ecenv -> local_theory -> local_theory

  type staterep
  val globals_all_addressed : bool Config.T
  val populate_globals : bool Config.T
  val record_globinits : bool Config.T

  val ctype_to_typ : Proof.context -> int ctype -> typ
  datatype var_sort = Local of (string * bool)
                    | NSGlobal
                    | AddressedGlobal
                    | UntouchedGlobal

  val create_state : csenv -> staterep

  val mk_thy_types :
      csenv -> bool -> bool -> local_theory ->
      (string * ((string * typ * int ctype * CType.attribute list) list * CType.attribute list)) list * local_theory
      

  val mk_thy_decls : string -> staterep -> 
      {mstate_ty : typ, gstate_ty : typ, owners : string list, 
       addressed_funs : string list, all_funs: string list} ->
      theory ->
      ((nm_info * typ * int ctype option * var_sort) list *
       (typ,term,thm list) Element.ctxt list * (typ * typ * typ list)) * theory

  val gen_umm_types_file : Proof.context -> bool -> csenv -> Path.T -> unit

  type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table
  val mk_mungedb : (nm_info * typ * int ctype option * var_sort) list ->
                   mungedb


  (* storing csenv's in the theory *)
  val store_csenv : string * csenv -> theory -> theory
  val get_csenv : theory -> string -> csenv option
  val map_csenv : string -> (csenv -> csenv) -> theory -> theory

  (* storing ghost-state types in the theory *)
  val store_ghostty : string * typ -> theory -> theory
  val get_ghostty : theory -> string -> typ option
  (* storing mungedb's in the theory *)
  val store_mungedb : string * mungedb -> theory -> theory
  val get_mungedb : theory -> string -> mungedb option

  val get_globals_data : typ -> typ -> theory -> {acc : term, upd : term,
    fields : (string * typ) list}
  val get_standard_globals : typ -> typ -> theory
    -> {hp: ((term * term) * (term * term)),
        phantom: ((term * term) * (term * term)),
        ghost: ((term * term) * (term * term))}

  val get_locals_data : typ -> typ -> theory -> {acc : term, upd : term}
  val get_global_exn_var_data : typ -> theory -> {acc : term, upd : term}

(*
   The isa_decl type corresponds to a program variable in a form that will be
   easy for Isabelle to process.

      vdecl (nm, ty, vsort)  nm is the name of a variable of type ty,
                             declared in function f if fname is Local
                             f, or a global: UntouchedGlobal if it is never
                             modified or addressed, NSGlobal if its
                             address is not taken, or AddressedGlobal
                             if it is.

   [create_state intinfo vars] returns a sequence of abstract Isabelle
   variable information.

   [mk_thy_decls decls] translates such a series into an operation on
   an Isabelle theory, creating various records ('myvars', 'globals',
   with fields corresponding to the variables

*)
  val union_variant: {non_canonical:bool} -> theory -> csenv -> xstring * string -> (typ * typ * typ) option
  val union_variant_types: {non_canonical:bool} -> theory -> csenv -> typ list
end;


structure CalculateState : CALCULATE_STATE =
struct

val generate_umm_types_file = Attrib.setup_config_bool @{binding "c_parser_generate_umm_types_file"} (K false) 

open Basics Absyn TermsTypes NameGeneration ProgramAnalysis Feedback

val globals_all_addressed = Attrib.setup_config_bool \<^binding>\<open>globals_all_addressed\<close> (K false)
val populate_globals = Attrib.setup_config_bool \<^binding>\<open>populate_globals\<close> (K false)
val record_globinits = Attrib.setup_config_bool \<^binding>\<open>record_globinits\<close> (K false)


 
fun define_enum_consts (CE {enumenv, ...}) lthy = let
  fun define1 (nm, (value, tyname_opt)) (acc,lthy) = let
    val rhs_v = IntInfo.numeral2w (Signed Int) value
    val typeinfo = case tyname_opt of NONE => "" | SOME s => " (of type "^s^")"
    val _ = informStr lthy (2, "Defining enumeration constant "^nm^typeinfo^
                         " to have value "^
                         Int.toString value^" (signed int)")
    val nm' = NameGeneration.enum_const_name nm
    val binding = Binding.name nm'
    val ((_, (_, th)), lthy) =
        Local_Theory.define ((binding, NoSyn),
                             ((Thm.def_binding binding, []), rhs_v))
                            lthy
    fun upd th t = th :: t
    val acc = case tyname_opt of
                NONE => acc
              | SOME nm => Symtab.map_default (nm, []) (upd th) acc
  in
    (acc, lthy)
  end
  val sfx = NameGeneration.enum_const_summary_lemma_sfx
  fun group_lemma (tynm, ths) lthy =
      (informStr lthy (2, "Adding "^Int.toString (length ths)^
                     " enum definitions for type "^ tynm);
       #2 (Local_Theory.note ((Binding.name(tynm ^ sfx), []), ths) lthy))

  val (tythms, lthy) = Symtab.fold define1 enumenv (Symtab.empty, lthy)
  val lthy = Symtab.fold group_lemma tythms lthy
in
  lthy
end

datatype isa_type = refty of (isa_type option * int ctype)
                  | recd of (string * int ctype)
                  | array of isa_type * int * int ctype
                  | existing of typ * int ctype
type isa_senv = isa_type rcd_env

datatype var_sort =
         Local of string * bool | NSGlobal | AddressedGlobal | UntouchedGlobal
type isa_var = (nm_info * isa_type * var_sort)
datatype isa_decl = vdecl of nm_info * isa_type * var_sort
type staterep = isa_decl list

fun isa_type_to_cty (refty (_, c)) = c
  | isa_type_to_cty (recd(_, c)) = c
  | isa_type_to_cty (array (_, _, c)) = c
  | isa_type_to_cty (existing(_, c)) = c

fun translate_inttype (ty : int ctype) =
  case ty of
    Signed x => existing (IntInfo.ity2wty (Signed x), ty)
  | Unsigned x => existing (IntInfo.ity2wty (Unsigned x), ty)
  | PlainChar => existing (IntInfo.ity2wty PlainChar, ty)
  | Bool => existing (IntInfo.ity2wty Bool, ty)
  | Ptr Void => refty (NONE, ty)
  | Ptr (Function _) => refty (NONE, ty)
  | Ptr ty0 => refty (SOME (translate_inttype ty0), ty)
  | Array(ty0, SOME sz) => array (translate_inttype ty0, sz, ty)
  | Array(_, NONE) => raise Fail "translate_inttype: incomplete array!"
  | StructTy s => recd (s, ty)
  | UnionTy s => recd (s, ty)
  | EnumTy _ => translate_inttype (Signed Int)
  | Ident _ => raise Fail "Should never happen: translate out typedefs"
  | Void => existing (@{typ unit}, ty)
  | Bitfield _ => raise Fail "Can't cope with bitfields"
  | _ =>
    raise Fail ("translate_type: can't cope with "^tyname ty)

val translate_type = translate_inttype

(* translate_vi creates a list of variables that need to be declared
   in the isabelle environment.  The information provided is the name
   of the variable, the "isa type", the name of the enclosing function
   (can be NONE to represent a global var, and the structure
   environment.

   For struct types, additional type declarations need to be made (the
   Isabelle record types need to be declared).  For pointer types,
   additional global variables need to be declared, these will be of a
   function type from a reference type to the type pointed to by the
   variable, and represent the heap.  This augmentation is done by
   augment_decls below.

 *)
fun translate_vi csenv = let
  val untoucheds = calc_untouched_globals csenv
  fun doit vi = let
  in
    case get_vtype vi of
      Function _ => NONE
    | ty => let
        val isaty = translate_type ty
        val k = get_mname vi
        val var_sort =
            case get_fname vi of
              SOME s => Local (s, is_addressed csenv (k, SOME s)) 
            | NONE => let
              in
                if XMSymTab.defined (get_addressed csenv) (k, NONE) then
                  AddressedGlobal
                else if MSymTab.defined untoucheds k then
                  UntouchedGlobal
                else
                  NSGlobal
              end
      in
        SOME (get_vi_nm_info csenv vi, isaty, var_sort)
      end
  end
in
  doit
end

fun isa_type_to_typ ctxt (ity : isa_type) = let
  fun m s = let
    val thy = Proof_Context.theory_of ctxt
    val known = (Syntax.parse_typ ctxt s; true) handle ERROR _ => false
    val f = if known then Sign.intern_type thy else Sign.full_name thy o Binding.name
  in
    f s
  end
  fun mk_array_size_ty sz =
    mk_numeral_type sz
in
  case ity of
    refty (NONE, _) => mk_ptr_ty unit
  | refty (SOME ity0, _) => mk_ptr_ty (isa_type_to_typ ctxt ity0)
  | recd (s, _) => Type (m s, [])
  | array (ity, sz, _) =>
    Type("Arrays.array", [isa_type_to_typ ctxt ity, mk_array_size_ty sz])
  | existing (ty, _) => ty
end

fun ctype_to_typ ctxt c0ty =
    isa_type_to_typ ctxt (translate_inttype c0ty)

fun create_state cse = let
  val trans = translate_vi cse
  fun innerfold vi acc =
      case trans vi of
        NONE => acc
      | SOME v => vdecl v :: acc
  fun outerfold (_,vlist) acc = acc |> fold innerfold vlist
  val vs = Symtab.fold outerfold (get_vars cse) []
in
  vs
end

fun union_variant {non_canonical} thy cse (name, fldname) =
  case AList.lookup (op =) (get_union_variants cse) name of 
    NONE => NONE
  | SOME struct_variants => (* union with multiple variants *)
      let
        val union_ty = Type (Sign.intern_type thy name, [])
        val (variant, (_, flds, _ , _)) = the (AList.lookup (op =) struct_variants fldname) |> hd
        val fld = the (AList.lookup (op =) flds fldname)
        val fld_ty = ctype_to_typ (Proof_Context.init_global thy) (fst fld)
        val variant_ty = Type (Sign.intern_type thy variant, [])
      in if non_canonical andalso variant = name then NONE else SOME (union_ty, variant_ty, fld_ty) end

fun union_variant_types {non_canonical} thy cse =
  let 
     val variants = get_union_variants cse
     fun mk_ty name = Type (Sign.intern_type thy name, []) 
     val canonicals = map (mk_ty o fst) variants 
     val all_variants = variants |> maps snd |> maps snd |> map fst |> map mk_ty 
  in if non_canonical then filter_out (member (op =) canonicals) all_variants else all_variants end

fun split_vars thy (lvars, gvars) dlist = let
  val split_vars = split_vars thy
in
  case dlist of
    [] => (List.rev lvars, List.rev gvars)
  | vdecl (s, ty, vsort) :: tail => let
      val tuple = (s, isa_type_to_typ (thy2ctxt thy) ty, SOME (isa_type_to_cty ty), vsort)
    in
      case vsort of
        Local _ => split_vars (tuple :: lvars, gvars) tail
      | _ => split_vars (lvars, tuple :: gvars) tail
    end
end

fun listvars f vns =
    case vns of
        [vn] => f vn
      | vn::rest => f vn ^ ", " ^ listvars f rest
      | [] => "<none>"

fun mk_fix ty n = (Binding.name n, SOME ty, NoSyn)

datatype umm_decl = umm_array of int ctype * int
                  | umm_struct of string * (string * (int ctype * CType.attribute list)) list * CType.attribute list * thm * thm
                  | umm_union of string * (string * (int ctype * CType.attribute list)) list * CType.attribute list * thm * thm
structure UMMKey =
struct
  type key = umm_decl
  fun ord (umm_array _, umm_struct _) = LESS
    | ord (umm_array _, umm_union _) = LESS
    | ord (umm_array p1, umm_array p2) = prod_ord (ctype_ord int_ord) int_ord (p1, p2)
    | ord (umm_union _, umm_array _) = GREATER
    | ord (umm_union _, umm_struct _) = LESS
    | ord (umm_union (u1, _, _, _, _), umm_union (u2, _, _, _, _)) = string_ord (u1, u2)
 
    | ord (umm_struct _, umm_array _) = GREATER
    | ord (umm_struct _, umm_union _) = GREATER
    | ord (umm_struct (s1, _, _, _, _), umm_struct (s2, _, _, _, _)) = string_ord (s1, s2)
end
structure UMMTab = Table(UMMKey)
local
  structure UMMFlip = FlipTable(structure Table = UMMTab)
in
val ummflip = UMMFlip.flip
end



fun burrow_split f xss = 
   fold_rev (fn (xs, ys) => fn (xss, yss) => (xs :: xss, ys :: yss)) (map f xss) ([], [])
   |> apply2 (filter_out null)


(*
 * Perform a topological sort of structures such that "parent" structures
 * appear after "child" structures (where a "parent" has a pointer to or
 * includes a "child" structure).
 *
 * Structures may be mutually dependent; in this case, the structures will
 * appear in the same list in the output.
 *)
fun get_sorted_structs prune cse =
let
  val union_structs = get_union_variants cse |> maps snd |> maps snd
  val rcds = get_senv cse @ union_structs 
       (* canonical variant of union (in union_structs) shall override the
        * corresponding original union entry in 'get_senv cse' with the same name. Should happen as
        * side effect of sorted_structs *) 
  val sorted_structs =
      if null rcds then []
      else let
          val (rcdmap,rcdnames) = (Symtab.empty, []) |>
              fold (fn (r as (s,_)) => fn (tab, nms) => (Symtab.update (s, r) tab, s::nms)) rcds;
          fun rcd_neighbours ptr (s, (kind, flds, _, _)) acc = let
            fun struct_refs ptr cty acc =
                case cty of
                  Ptr ty' => if ptr then struct_refs ptr ty' acc else acc
                | StructTy s' => Symtab.cons_list (s,s') acc
                | UnionTy s' => Symtab.cons_list (s,s') acc
                | Array(ty', _) => struct_refs ptr ty' acc
                | _ => acc
          in
            acc |> fold (fn (_, (ty,_)) => struct_refs ptr ty) flds
          end
          val inclusion_graph = Symtab.empty |> fold (rcd_neighbours true) rcds
          val inclusion_graph_structural = Symtab.empty |> fold (rcd_neighbours false) rcds
          val inverse_graph = flip_symtab inclusion_graph
          val inverse_graph_structural = flip_symtab inclusion_graph_structural
          open Topo_Sort
          val sorted_structural = topo_sort {cmp = string_ord,
                                   graph = Symtab.lookup_list inclusion_graph_structural,
                                   converse = Symtab.lookup_list inverse_graph_structural}
                                  rcdnames |> flat
          val sorted0 = topo_sort {cmp = string_ord,
                                   graph = Symtab.lookup_list inclusion_graph,
                                   converse = Symtab.lookup_list inverse_graph}
                                  rcdnames

          fun sort_structural [] = []
            | sort_structural [x] = [x]
            | sort_structural clique = filter (member (op =) clique) sorted_structural 

          val sorted1 = map sort_structural sorted0
        in
          map (map (the o Symtab.lookup rcdmap)) sorted1
        end
  val used_types = ProgramAnalysis.get_usedtypes cse
in
  sorted_structs
  |> burrow_split (List.partition (fn item => not prune 
       orelse Binaryset.member (used_types, CType.type_of_rcd item) 
       orelse member (op =) union_structs item))

end



(*
 * Generate an output file "umm_types.txt" that contains information about
 * structures in the input C file.
 *
 * This is required by certain external tools, such as the bitfield generator.
 *)
fun gen_umm_types_file ctxt prune cse outfile = if not (Config.get ctxt generate_umm_types_file) then () else
let
  val num_ty_string = Word_Lib.dest_binT #> string_of_int

  fun str_of_kind Struct = "struct" 
    | str_of_kind (Union _) = "union"

  fun write_one strm (recname, (kind, flds, _, _)) = let
    fun isa_to_string (refty (NONE, _)) = "Ptr Unit"
      | isa_to_string (refty (SOME ty, _)) = "Ptr " ^ isa_to_string ty
      | isa_to_string (recd (s, _)) = s
      | isa_to_string (array (ty, n, _)) = "Array " ^ (isa_to_string ty) ^
                                           " " ^ (Int.toString n)
      | isa_to_string (existing (Type(@{type_name "word"},
                                  [Type (@{type_name "Signed_Words.signed"}, [n])]), _)) =
            "Signed_Word " ^ num_ty_string n
      | isa_to_string (existing (Type(@{type_name "word"},
                                      [n]), _)) = "Word " ^ num_ty_string n
      | isa_to_string _ = error "Unexpected type in isa_to_string"

    fun do_one_fld kind (fldname, (fldty, _)) =
      let
        val is_inactive = case kind of 
           Union active => if member (op =) active fldname then "" else " (* inactive *)"
         | _ => ""
      in
        File_Stream.output strm ("\t" ^ fldname ^ ":" ^
                             isa_to_string (translate_type fldty) ^ is_inactive ^ "\n")
      end

    val _ = File_Stream.output strm (str_of_kind kind ^ " " ^ recname ^ "\n")
    val _ = app (do_one_fld kind) flds
  in
    File_Stream.output strm "\n"
  end

  fun unused_msg (recname, (kind, _, _, _)) =
    informStr ctxt (1, "omitting unused " ^ str_of_kind kind ^ " \"" ^ recname ^ "\"")
  
  val (sorted_structs, ommitted_structs) = get_sorted_structs prune cse |> apply2 flat
  val _ = outfile |> File_Stream.open_output (fn outstrm => app (write_one outstrm) sorted_structs)
  val _ = app unused_msg ommitted_structs
in
  ()
end

val outfilename = \<^path>\<open>umm_types.txt\<close>


    
fun zip_nested [] [] = []
  | zip_nested (xs::xss) (ys::yss) = (xs ~~ ys) :: zip_nested xss yss
  | zip_nested _ _ = raise ListPair.UnequalLengths;

fun mk_thy_types cse install prune (lthy:local_theory) = let
  (* Make the necessary theory declarations to make the C file's types work
     in Isabelle.  There are two phases.

     Phase 0:
       For arrays, declaration of the numCopy types corresponding to
       the sizes of the various arrays.  This can be done before
       anything else happens, as it is not dependent on any other types.

       For structs, the basic declaration of the corresponding record
       type, using the RecursiveRecordPackage.  This is complicated by the
       fact that multiple structs may be mutually recursive.  So you
       have to figure out which ones, and declare them all together.
       This requires a topological sort of the struct declarations.
       This phase is also dependent on array sizes having been
       declared correctly because a struct's field may be an array,
       and this requires that array's size type to be declared
       already.

     Phase1:
       UMM property proofs.  These have to happen in the order of
       declaration from the C file (which is reflected in the "state"
       parameter).

     Also return a list of all the record declarations that were made
     for consumption by later phases of the translation.

  *)

  val structs_and_unions = get_sorted_structs prune cse |> fst 

  open MemoryModelExtras
  open UserTypeDeclChecking
  val umm_prfstate = initial_state
  fun check_union n = ProgramAnalysis.sizeof cse (UnionTy n) (* might raise error *)

  fun canonical_union_variant name active flds =
    case try (CType.single_variant name active) flds of 
      SOME flds' => flds'
    | NONE =>
        error ("canonical variant for union " ^ name ^ " did not override original union entry")

  fun single_variant_union_fields n (Union active) flds =
       let
         val _ = check_union n
       in
         canonical_union_variant n active flds
       end
    | single_variant_union_fields n _ flds = flds
 
  fun new_rcdinfo' ctxt (recname,(kind,flds, _, attrs))  = 
    let
      val flds = single_variant_union_fields recname kind flds
      fun fldtys (fldname, (cty, attrs)) = (fldname, ctype_to_typ ctxt cty, cty, attrs)
    in
      (recname, (map fldtys flds, attrs))
    end

  fun new_rcdinfo ctxt (recname,flds, attrs)  = let
    fun fldtys (fldname, (cty, attrs)) = (fldname, ctype_to_typ ctxt cty, cty, attrs)
  in
    (recname, (map fldtys flds, attrs))
  end

  fun rcddecls_phase0 recflds lthy = 
      let
        val _ =
            informStr lthy (2, "Defining isabelle type(s) corresponding to \
                         \struct group:")
        val _ = app (fn (recname, (Struct, flds, _ , _)) =>
                        informStr lthy (2, "  struct " ^ recname ^ ", with fields: " ^
                                      listvars #1 flds)
                       | (recname, (Union active, flds, _, _)) =>
                        informStr lthy (2, " union " ^ recname ^ ", with variant: " ^ 
                                      listvars #1 (canonical_union_variant recname active flds)))
                    recflds

        fun mk_rp_fld ctxt (fldname,(cty,_)) = {fldname = fldname,
                                           fldty = ctype_to_typ ctxt cty}
        fun mk_rp_recd ctxt (recname, (Struct, flds, _, _)) =
              {record_name = recname, fields = map (mk_rp_fld ctxt) flds}
          | mk_rp_recd ctxt (recname, (Union active, flds, _, _)) =
              {record_name = recname, fields = map (mk_rp_fld ctxt) (canonical_union_variant recname active flds)}

        val def_lthy = lthy
          |> More_Local_Theory.in_theory (RecursiveRecordPackage.define_record_type (map (mk_rp_recd lthy) recflds))
      in
        def_lthy 
        |> fold UMM_Proofs.c_type_name_instantiation (map fst recflds)
        |> fold_map UMM_Proofs.c_type_instantiation (map (new_rcdinfo' def_lthy) recflds)
      end
  
  val (thms, lthy) = if install then lthy |> fold_map rcddecls_phase0 structs_and_unions else ([], lthy)

  val flat_structs_and_unions = flat (zip_nested structs_and_unions thms)

  val structs = flat_structs_and_unions |> map_filter 
       (fn ((n, (kind, flds, _, attrs)), (tag_def_thm, typtag_thm)) => case kind of Struct => 
         SOME (n, flds, attrs, tag_def_thm, typtag_thm) | _ => NONE);

  val unions = flat_structs_and_unions |> map_filter 
       (fn ((n, (kind, flds, _, attrs)), (tag_def_thm, typtag_thm)) => case kind of Union active => 
         SOME (n, single_variant_union_fields n kind flds, attrs, tag_def_thm, typtag_thm) | _ => NONE);

  (* Yuck, sorry *)
  val () = gen_umm_types_file lthy prune cse outfilename


  val arrays = List.filter (fn (ty, sz) => sz <> 0 andalso Binaryset.member (get_usedtypes cse, ty))
                           (Binaryset.listItems (get_array_mentions cse))
  val umm_events = let
    val evs = map umm_array arrays @ map umm_struct structs @ map umm_union unions
  in
    if null evs then []
    else let
        val umm_struct_map = Symtab.empty 
          |> fold (fn (r as (s, _, _, _, _)) => Symtab.update (s,umm_struct r)) structs
        val umm_union_map = Symtab.empty
          |> fold (fn (r as (s, _, _, _, _)) => Symtab.update (s,umm_union r)) unions
        val umm_array_set = (Binaryset.empty UMMKey.ord)
          |> fold (fn a => fn acc => Binaryset.add(acc,umm_array a)) arrays
        fun toEv ty =
            case ty of
              Array (ty, SOME sz) => let
                val u = umm_array(ty,sz)
              in
                if Binaryset.member(umm_array_set, u) then SOME u else NONE
              end
          | StructTy s => Symtab.lookup umm_struct_map s
          | UnionTy s => Symtab.lookup umm_union_map s
          | _ => NONE
        fun umm_included uev =
            case uev of
              umm_array (ty, _) => [ty]
            | umm_struct(_, flds, _, _, _) => map (#1 o #2) flds
            | umm_union(_, flds, _, _, _) => map (#1 o #2) flds
        val inclusion = UMMTab.empty
          |>  fold (fn u => UMMTab.update (u, List.mapPartial toEv (umm_included u))) evs
        val converse = ummflip inclusion
        val sorted_evs = Topo_Sort.topo_sort {graph = UMMTab.lookup_list inclusion,
                                              converse = UMMTab.lookup_list converse,
                                              cmp = UMMKey.ord}
                                             evs
        val _ = List.all (fn l => length l = 1) sorted_evs orelse
                error "Topological sort of object inclusion includes a loop"
      in
        map hd sorted_evs
      end
  end

  fun structdecl_phase1 (p as (recname, flds, attrs, tag_def_thm, typ_info_t_thm), (lthy, st, rcdacc)) = let
    val rcdinfo = new_rcdinfo lthy (recname, flds, attrs) 
    val (st, lthy1) =
        if install then
          (informStr lthy (2, "Proving UMM properties for struct "^recname);
           struct_type cse {struct_type = rcdinfo, tag_def_thm = tag_def_thm, typ_info_t_thm = typ_info_t_thm,state = st}
                       lthy)
        else (st, lthy)
  in
    (lthy1, st, rcdinfo :: rcdacc)
  end

  fun arraytype_phase1 ((cty, n), (lthy, st, rcdacc)) = let
      val (st', lthy') =
          if install then
              array_type cse
                         {element_type = ctype_to_typ lthy cty, array_size =  n,
                          state = st}
                         lthy
          else
              (st, lthy)
  in
      (lthy', st', rcdacc)
  end

  fun uniondecl_phase1 (p as (recname, _ (* flds *), _,_,_), (lthy, st, rcdacc)) = 
    structdecl_phase1 (p, (lthy, st, rcdacc))
   

  fun phase1 idecl acc =
      case idecl of
        umm_array ai => arraytype_phase1 (ai, acc)
      | umm_struct si => structdecl_phase1 (si, acc)
      | umm_union ui => uniondecl_phase1 (ui, acc) 

  val (lthy, final_state, rcdinfo0) = (lthy, umm_prfstate, [])
    |> fold phase1 umm_events
  val lthy = lthy |> install ? (UserTypeDeclChecking.finalise final_state) 
in
  (List.rev rcdinfo0, lthy)
end

fun simple s = {isa_name = MString.mk s, src_name = s, alias = false}

fun pretty_recdef thy nm vars =
    Pretty.big_list
        ("Defining record: " ^ nm ^ " =")
        (map (fn (nm,ity,_,_) =>
                 Pretty.str (MString.dest (#isa_name nm) ^ " :: " ^
                             Syntax.string_of_typ (thy2ctxt thy) ity))
             vars)
    |> Pretty.string_of |> tracing;

fun categorise_globals (alladdressed, popglobs) l = let
  fun recurse (acc as (ut, ns, ad)) l =
    case l of
      [] => acc
    | (g as (_, _, _, vsort)) :: rest => let
      in
        if not alladdressed orelse not popglobs then let
            val vsort = if alladdressed then AddressedGlobal else vsort
          in
            case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen"
            | UntouchedGlobal => recurse (g::ut,      ns,    ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns,    ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
          end
        else
          case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen #2"
            | UntouchedGlobal => recurse (g::ut,      ns, g::ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns, g::ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
      end
in
  recurse ([],[],[]) l
end

fun mk_thy_decls prog_name state {owners, mstate_ty = pmstate_ty, gstate_ty, addressed_funs, all_funs} thy = let
  val rest = state
  fun declare_vars thy = let
    val (lvars, gvars) = split_vars thy ([], []) rest
    open NameGeneration
    fun mk_globals_rcd thy = let
      val (_(* utglobs *), nsglobs, adglobs (* adglobs *)) =
          (* untouched globals, Norbert Schirmer Globals, addressed globals *)
          categorise_globals (Config.get_global thy globals_all_addressed,
                              Config.get_global thy populate_globals)
                             gvars
      
      val _ = if not (null gvars) then pretty_recdef thy "globals" nsglobs
              else ()
      val gflds =
          [(Binding.name global_heap_var, MemoryModelExtras.extended_heap_ty, NoSyn),
           (Binding.name (global_var phantom_state_name), pmstate_ty, NoSyn),
           (Binding.name (global_var ghost_state_name), gstate_ty, NoSyn)] @
          map (fn ({isa_name,...}, ty, _, _) =>
                  (Binding.name (global_var (MString.dest isa_name)), ty, NoSyn))
              nsglobs @
          (if null owners then []
           else [(Binding.name (global_var owned_by_fn_name), nat, NoSyn)])
      val thy =
          Record.add_record {overloaded=false}
                           ([], Binding.name NameGeneration.global_rcd_name) NONE
                            gflds thy
      val fullrecname = Sign.intern_type thy NameGeneration.global_ext_type
      val thy = MemoryModelExtras.check_global_record_type fullrecname thy
      val ((((S, G), known_function)), thy) = thy
        |> Theory.specify_const (((Binding.make (NameGeneration.stack_addrs, \<^here>), @{typ "addr set"})), Mixfix.NoSyn)
        ||>> Theory.specify_const (((Binding.make (NameGeneration.global_addrs, \<^here>), @{typ "addr set"})), Mixfix.NoSyn)
        ||>> Theory.specify_const (((Binding.make (NameGeneration.known_function, \<^here>), @{typ "unit ptr \<Rightarrow> bool"})), Mixfix.NoSyn)


      val ctxt = Proof_Context.init_global thy
      val params = globals_stack_heap_raw_state_params State ctxt
      val [hrs, hrs_upd] = map Utils.dummy_schematic [#hrs params, #hrs_upd params] 
      val expr = ([(@{locale globals_stack_heap_raw_state}, ((NameGeneration.state_rcd_name, true),
           (Expression.Positional (map SOME ([hrs, hrs_upd, S, G])), [])))], []) 
       
      val thy = thy |> Named_Target.theory_init
        |> Interpretation.global_interpretation expr []
        |> Proof.global_terminal_proof ((Method.Basic (fn ctxt =>  SIMPLE_METHOD (
            (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN 
               ALLGOALS (asm_full_simp_tac (ctxt addsimps 
                 @{thms hrs_mem_def hrs_mem_update_def hrs_htd_def hrs_htd_update_def case_prod_unfold}))))), 
            Position.no_range), NONE) 
        |> Local_Theory.exit_global

      val params = globals_stack_heap_raw_state_params Globals ctxt
      val [hrs, hrs_upd] = map Utils.dummy_schematic [#hrs params, #hrs_upd params] 
      val expr = ([(@{locale globals_stack_heap_raw_state}, ((NameGeneration.global_rcd_name, true),
           (Expression.Positional (map SOME ([hrs, hrs_upd, S, G])), [])))], []) 
       
      val thy = thy |> Named_Target.theory_init
        |> Interpretation.global_interpretation expr []
        |> Proof.global_terminal_proof ((Method.Basic (fn ctxt =>  SIMPLE_METHOD (
            (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN 
               ALLGOALS (asm_full_simp_tac (ctxt addsimps 
                 @{thms hrs_mem_def hrs_mem_update_def hrs_htd_def hrs_htd_update_def case_prod_unfold}))))), 
            Position.no_range), NONE) 
        |> Local_Theory.exit_global

      val globalsT = Proof_Context.read_typ (Proof_Context.init_global thy) NameGeneration.global_rcd_name
      val globals_fields = Record.get_extT_fields thy globalsT |> fst
      val ((_, (t_hrs, t_hrs_update))::globals) = globals_fields  
        |>  map (fn (n, T) => 
              (Long_Name.base_name n, 
                (Const (n, globalsT --> T),  
                Const (n ^ Record.updateN, (T --> T) --> (globalsT --> globalsT)))))

      fun interpret_global_field (n, (get, upd)) thy =
        let
          val expr = ([(@{locale heap_raw_state_global}, ((n, true),
           (Expression.Positional (map SOME ([t_hrs, t_hrs_update, get, upd])), [])))], []) 
        in
          thy |> Named_Target.theory_init
          |> Interpretation.global_interpretation expr []
          |> Proof.global_terminal_proof ((Method.Basic (fn ctxt =>  SIMPLE_METHOD (
            (Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN 
               ALLGOALS (asm_full_simp_tac ctxt)))), 
            Position.no_range), NONE) 
          |> Local_Theory.exit_global
        end

      val thy = thy |> fold interpret_global_field globals
     
      fun declare_fun_ptr fname thy =
        let
          val fname = NameGeneration.fun_ptr_name fname
          val b = Binding.make (fname, \<^here>) |> Binding.qualify true prog_name
        in
          thy |> Theory.specify_const ((b, @{typ "unit ptr"}), Mixfix.NoSyn)
        end
      val (fun_ptrs, thy) = thy |> fold_map declare_fun_ptr addressed_funs
      val remaining_funs = filter_out (member (op =) addressed_funs) all_funs
      val (_, thy) = thy |> fold_map declare_fun_ptr remaining_funs

      fun mk_fun_ptr_guard (p, fname) = ((Binding.make (fname ^ "_fnptr_guard", \<^here>), @{attributes [fun_ptr_simps]}), 
            [(\<^instantiate>\<open>p = \<open>p\<close> in prop \<open>c_fnptr_guard (p::unit ptr)\<close>\<close>, [])])

      val all_distinct = ((Binding.make ("all_distinct", \<^here>), @{attributes [fun_ptr_distinct]}), 
            [(\<^instantiate>\<open>t = \<open>DistinctTreeProver.mk_tree I @{typ "unit ptr"} fun_ptrs\<close> 
               in prop \<open>all_distinct t\<close> for t:: \<open>unit ptr tree\<close>\<close>, 
             [])])

      fun declare_addressed_global g thy =
        let
          val T = (mk_ptr_ty o #2) g
          val name = (global_var o  MString.dest o #isa_name o #1) g
          val b = Binding.make (name, \<^here>) 
        in
          thy |> Theory.specify_const ((b, T), Mixfix.NoSyn)
        end
      val (global_ptrs, thy) = thy |> fold_map declare_addressed_global adglobs
    in
      (thy, [Element.Fixes (map (mk_fix nat) owners), 
             Element.Assumes (map mk_fun_ptr_guard (fun_ptrs ~~ addressed_funs)),
             Element.Assumes [all_distinct]])
    end
    val lvars = lvars
    val (thy, globs) = mk_globals_rcd thy
    val ctxt = Proof_Context.init_global thy
    val globty = Proof_Context.read_typ ctxt NameGeneration.global_rcd_name
    val locty = localsT
    val statetype = Proof_Context.cert_typ ctxt 
           (Type("CProof.state", [globty, locty, @{typ exit_status}]))
    val styargs = [statetype, IsabelleTermsTypes.procT, StrictC_errortype_ty]
    fun declare_gamma thy =
      let
        val b = Binding.make (HP_TermsTypes.gammaN, \<^here>) |> Binding.qualify false prog_name
        val T = HP_TermsTypes.mk_gamma_ty styargs
      in 
        thy |> Theory.specify_const ((b, T), Mixfix.NoSyn)
      end
    val (gamma, thy) = declare_gamma thy
  in
    ((lvars @ gvars, globs, (globty, locty, styargs)), thy)
  end
in
  declare_vars thy
end

type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table

fun mk_mungedb l = let
  open CNameTab
  fun foldthis (nmi,ty,cty,vsort) tab = let
    val fnm_opt = case vsort of Local (s, _) => SOME s | _ => NONE
  in
    update ({varname = #isa_name nmi, fnname = fnm_opt},
            (#isa_name nmi, ty, cty,vsort))
           tab
  end
in
  Basics.fold foldthis l empty
end

structure csenvData = Theory_Data(
  type T = csenv Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_csenv (s,cse) =
    csenvData.map (Symtab.update(s,cse))
val get_csenv = Symtab.lookup o csenvData.get
fun map_csenv s f = csenvData.map (Symtab.map_entry s f)

structure ghostData = Theory_Data(
  type T = typ Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_ghostty (s, ty) =
    ghostData.map (Symtab.update(s,ty))
val get_ghostty = Symtab.lookup o ghostData.get

structure mungeDBs = Theory_Data(
  type T = mungedb Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun store_mungedb (s, ty) = mungeDBs.map (Symtab.update (s,ty))
val get_mungedb = Symtab.lookup o mungeDBs.get

fun get_globals_data statety globty thy = let
    val acc = Sign.intern_const thy "state.globals"
    val upd = Sign.intern_const thy (suffix Record.updateN "state.globals")
    val acc = Const (acc, statety --> globty)
    val upd = Const (upd, (globty --> globty) --> statety --> statety)
    val (flds, _) = Record.get_recT_fields thy globty
  in {acc = acc, upd = upd, fields = flds} end

fun get_locals_data statety locty thy = let
    val acc = Sign.intern_const thy "state_locals.locals"
    val upd = Sign.intern_const thy (suffix Record.updateN "state_locals.locals")
    val acc = Const (acc, statety --> locty)
    val upd = Const (upd, (locty --> locty) --> statety --> statety)
  in {acc = acc, upd = upd} end

fun get_global_exn_var_data statety thy = let
    val acc = @{const_name "global_exn_var'_'"}
    val upd = @{const_name "global_exn_var'_'_update"}
    val exty =  HP_TermsTypes.c_exntype_ty
    val acc = Const (acc, statety --> exty)
    val upd = Const (upd, (exty --> exty) --> statety --> statety)
  in {acc = acc, upd = upd} end




fun get_standard_globals statety globty thy = let
    val data = get_globals_data statety globty thy
    fun fld nm = let
        val flds = filter (fn (fnm, ty) => Long_Name.base_name fnm = nm)
          (#fields data)
        val (fldnm, ty) = case flds of [v] => v
          | [] => error ("could not find " ^ nm ^ " in global fields.")
          | _ => error ("multiple match for " ^ nm ^ " in global fields.")
        val acc = Const (fldnm, globty --> ty)
        val upd = Const (fldnm ^ Record.updateN,
            (ty --> ty) --> globty --> globty)
        val acc' = Abs ("s", statety, acc $ (#acc data $ Bound 0))
        val upd' = Abs ("u", ty --> ty, #upd data $ (upd $ Bound 0))
      in ((acc, upd), (acc', upd')) end
  in {hp = fld global_heap_var,
    phantom = fld (global_var phantom_state_name),
    ghost = fld (global_var ghost_state_name)}
  end

end (* struct *)

(* the string "local variables:" that appears a few lines above this was
   confusing emacs.  By adding the form-feed character below, I ensure that
   this no longer happens.  In other words, don't delete the form-feed! *)


(* Local variables: *)
(* End: *)
