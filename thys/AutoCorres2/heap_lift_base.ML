(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Construct necessary infrastructure to allow heap lifting to take place.
 * This creates the new globals record; the proofs relating it with the old
 * globals will be performed in HeapLift.
 *)

structure HeapLiftBase =
struct

structure Goal = struct

open Goal

fun prove_future ctxt fixes asms goal tac =
   let
     val single_threaded = ctxt |> AutoCorres_Options.Options_Proof.get |> AutoCorres_Options.get_single_threaded
   in
     case single_threaded of
       SOME (true) => Utils.timeit_msg 1 ctxt (fn _ => "Proof: " ^ Syntax.string_of_term (snd (Variable.add_fixes fixes ctxt)) goal ^ "\n ") (fn _ =>
                          Goal.prove ctxt fixes asms goal tac)
     | _ => Goal.prove_future ctxt fixes asms goal tac
   end

end

type addressable_fields_info =
  {addressable:     (string * typ) list list, (* path to a fields within a structure that might be addressed (address-of)*)
   not_addressable: (string * typ) list list  (* path to fields that are not addressed *)
};

type locale_interpretation =
{
  locale: string,
  qualifier: string,
  qualifier_mandatory: bool,
  params: term list
}

fun interpret (data : locale_interpretation) (tac : Proof.context -> tactic) =
  let
    val expr = ([(#locale data, ((#qualifier data, #qualifier_mandatory data),
       (Expression.Positional (map SOME (#params data)), [])))], [])
  in
    Interpretation.global_interpretation expr []
    #> Proof.global_terminal_proof
      ((Method.Basic (fn ctxt => SIMPLE_METHOD (tac ctxt)), Position.no_range), NONE)
  end

local
  val fields_ord = list_ord (prod_ord fast_string_ord Term_Ord.typ_ord)
in
fun addressable_fields_info_ord ({addressable = ass1, not_addressable = bss1},  {addressable = ass2, not_addressable = bss2}) =
  prod_ord (list_ord fields_ord) (list_ord fields_ord) ((ass1, bss1), (ass2, bss2))
end

type path_info = {root_typ: typ, path: (string * typ) list}

fun string_of_path path =
  map (Long_Name.base_name o fst) path |> space_implode "."

fun path_ord ({root_typ = T1, path = ps1},  {root_typ = T2, path = ps2}) =
  prod_ord Term_Ord.typ_ord (list_ord (prod_ord fast_string_ord Term_Ord.typ_ord)) ((T1, ps1), (T2, ps2))

type heap_field_info = {
  hget: term,
  hupd: term,
  hvalid: term,
  atomic_upds : term Ord_List.T,
  pointer_lense_axiom : thm
}

type field_info = {
  name : string,
  field_type : typ,
  getter : term,
  setter : term
};

type struct_info = {
  name : string,
  struct_type : typ,
  field_info : field_info list
};

type derived_thms = {
  getter: thm,
  setter: thm,
  valid: thm
}

type heap_info =
{
  globals_type : typ,
  old_globals_type : typ,
  heap_typing: term,
  heap_typing_update: term,
  open_types_T: term,
  heap_types : typ list, (* ordered from fundamental to derived heaps respecting dependencies *)
  heap_tab: {getter: term, setter: term, valid: term} Typtab.table,
  heap_getters : term Typtab.table,
  heap_setters : term Typtab.table,
  heap_valid_getters : term Typtab.table,
  ptr_valids : (typ * (term * thm * thm)) list,
  global_fields : (string * string * typ) list,
  global_field_getters : (term * term) Symtab.table,
  global_field_setters : (term * term) Symtab.table,
  lift_fn_name : string,
  lift_fn_thm : thm,
  lift_fn_full : term,
  dummy_state : term,
  lift_fn_simp_thms : thm list,
  structs : struct_info Symtab.table,
  struct_types : struct_info Typtab.table,
  pointwise_to_heapwide_thms : thm list,
  lifted_globals_equality : thm
};

type heap_lift_setup =
{
  heap_info : heap_info,
  (* Thms that depend only on heap types and can be pre-generated. *)
  (* Groups of instantiation lemmas. fixme: does cross_instantiate really need grouping? *)
  lifted_heap_lemmas : thm list list,
  (* Empty if no syntax consts have been defined yet *)
  heap_syntax_rewrs : thm list
};


local
    fun get_concr @{term_pat "L2Tcorres _ _ ?C"} = C
      | get_concr @{term_pat "abs_guard _ _ ?C"} = C
      | get_concr @{term_pat "abs_expr _ _ _ ?C"} = C
      | get_concr @{term_pat "abs_modifies _ _ _ ?C"} = C
      | get_concr @{term_pat "struct_rewrite_guard _ ?C"} = C
      | get_concr @{term_pat "struct_rewrite_expr _ _ ?C"} = C
      | get_concr @{term_pat "struct_rewrite_modifies _ _ ?C"} = C
      | get_concr t = error ("prune_unused_bounds_hl_tac, unexpected term: " ^ @{make_string} t)
in
val prune_unused_bounds_hl_tac = Utils.prune_unused_bounds_from_concr_tac get_concr
end

(* Return the function for fetching an object of a particular type. *)
fun get_heap_getter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_getters heap_info) T of
    SOME x => x
  | NONE => Utils.invalid_typ "heap type for getter" T

(* Return the function for updating an object of a particular type. *)
fun get_heap_setter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_setters heap_info) T of
    SOME x => x
  | NONE => Utils.invalid_typ "heap type for setter" T

(* Return the function for determining if a given pointer is valid for a type. *)
fun get_heap_valid_getter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_valid_getters heap_info) T of
    SOME x => x
  | NONE => Utils.invalid_typ "heap type for valid getter" T

(* Save heap information into the theory. *)
structure HeapInfo = Theory_Data(
  type T = heap_lift_setup Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true)
)

fun autofix_prove_future ctxt fixes asms goal tac =
  let
    val (goal'::asms', ctxt') = Variable.import_terms false (goal :: asms) ctxt
  in
    Goal.prove_future ctxt' fixes asms' goal' tac
    |> singleton (Variable.export ctxt' ctxt)
    |> Drule.zero_var_indexes
  end

fun triangle [] : ('a * 'a) list = []
  | triangle (x :: xs) = map (rpair x) xs @ triangle xs

datatype addressable_kind =
    All_Addressable of (string * typ) list
  | Some_Addressable of (string * typ) list list
  | None_Addressable

fun is_All_Addressable (All_Addressable _) = true
  | is_All_Addressable (Some_Addressable _) = false
  | is_All_Addressable None_Addressable = false

(*
 * Attempt to generate a pleasant name for the record
 * field name for the given heap.
 *
 *   word32        => heap_w32
 *   signed word32 => heap_w32
 *   word32 ptr    => heap_w32_ptr
 *   node_C ptr    => heap_node_ptr
 *)
local

(* Convert a numerical type back into an integer. *)
fun get_num_type x =
  case (dest_Type x) of
      (@{type_name "Numeral_Type.num0"}, _) => 0
    | (@{type_name "Numeral_Type.num1"}, _) => 1
    | (@{type_name "Numeral_Type.bit0"}, [T])
        => 2 * get_num_type T
    | (@{type_name "Numeral_Type.bit1"}, [T])
        => 2 * get_num_type T + 1
    | (@{type_name "Signed_Words.signed"}, [T])
        => get_num_type T
    | _ => raise TYPE ("name_from_type/get_num_type", [x], [])

fun get_index_type x =
  case x of
    Type _ => string_of_int (get_num_type x)
  | TFree (n, _) => n
  | _ => raise TYPE ("name_from_type/get_index_type", [x], [])

in

fun name_from_type x =
  case (dest_Type x) of
       (@{type_name "Word.word"}, [x])
         => "w" ^ (string_of_int (get_num_type x))
     | (@{type_name "ptr"}, [x])
         => (name_from_type x) ^ "'ptr"
     | (@{type_name "array"}, [x,y])
         => (name_from_type x) ^ "'array_" ^ (get_index_type y)
     | (x, _) => (Long_Name.base_name x)

fun name_with_signed_from_type x =
  case (dest_Type x) of
       (@{type_name "Word.word"}, [x]) =>
        (case (dest_Type x) of
          (@{type_name "Signed_Words.signed"}, [x]) => "s" ^ (string_of_int (get_num_type x))
        | _ =>  "w" ^ (string_of_int (get_num_type x)))
    | (@{type_name "ptr"}, [x]) => (name_with_signed_from_type x) ^ "'ptr"
    | (@{type_name "array"}, [x,y]) => (name_with_signed_from_type x) ^ "'array_" ^ (get_index_type y)
    | (x, _) => (Long_Name.base_name x)

end

fun is_word (Type (@{type_name "Word.word"}, _)) = true
  | is_word _ = false

fun pointwise ctxt setter =
  \<^infer_instantiate>\<open>setter = setter in term \<open>\<lambda>p f. setter (\<lambda>h. h(p := f (h p)))\<close>\<close> ctxt

fun pointwise_upd ctxt setter =
  \<^infer_instantiate>\<open>setter = setter in term \<open>\<lambda>p f. setter (upd_fun p f)\<close>\<close> ctxt

fun dest_pointwise @{term_pat \<open>\<lambda>p f. ?setter (\<lambda>h. h(p := f (h p)))\<close>} = SOME setter
  | dest_pointwise @{term_pat \<open>\<lambda>p f. ?setter (upd_fun p f)\<close>} = SOME setter
  | dest_pointwise _ = NONE

(*
 * Determine what types we will need for the split heap to support the given
 * term.
 *)
fun get_term_heap_types ctxt t =
let
  fun is_ptr_type T =
    case T of
        Type (@{type_name "ptr"}, [_]) => true
      | _ => false
in
  case t of
      (t as Abs _) => Utils.concrete_abs' ctxt t |> #1 |> get_term_heap_types ctxt
    | a $ b => get_term_heap_types ctxt a @ get_term_heap_types ctxt b
    | a => (body_type (fastype_of a) :: binder_types (fastype_of a))
           |> filter is_ptr_type
           |> map (dest_Type #> snd #> hd)
end

fun typ_of_path [] = error ("type_of_path: empty path")
  | typ_of_path fs = snd (List.last fs)

(* Determine what heap types the given program accesses. *)
fun get_program_heap_types prog_info addressable_fields fn_infos gen_word_heaps lthy =
let
  (* Map the type "T" into a (possibly different) type that should appear in
   * our new heap. *)
  fun map_heap_type T =
    case T of
      (* Signed words are converted to standard words on the heap. *)
        Type (@{type_name "Word.word"},
          [Type (@{type_name "Signed_Words.signed"}, x)]) =>
            Type (@{type_name "Word.word"}, x)

      (* Pointers are valid if their inner type is valid. *)
      | Type (@{type_name "ptr"}, [x])
          => Type (@{type_name "ptr"}, [map_heap_type x])

      (* Arrays are valid if their inner type is valid. *)
      | Type (@{type_name "array"}, [x, _])
          => map_heap_type x

      | _ => T

  (* Process a function. *)
  fun process fn_name =
      (* Fetch body of "fn_name". *)
      the (Symtab.lookup fn_infos fn_name)
      |> FunctionInfo.get_definition
      |> Thm.concl_of
      |> Utils.rhs_of_eq

      (* Fetch types from function body. *)
      |> get_term_heap_types lthy

      (* Fiddle with types if necessary. *)
      |> map map_heap_type
      |> Typset.make

      (* Remove the "void" heap if it exists. *)
      |> Typset.subtract (Typset.make [@{typ "unit"}])

  val addressableTs = fold (fn (_, {addressable = addrs, ...}) => fold (fn path =>
      let
        val (_, (_, T)) = split_last path
      in
        Typset.insert T
      end) addrs) addressable_fields (Typset.make [])

  (* Generate all word heaps if desired. *)
  val word_typs = if not gen_word_heaps then Typset.empty else
                      Typset.make [@{typ word8}, @{typ word16}, @{typ word32}, @{typ word64}]
  val union_variants = CalculateState.union_variant_types {non_canonical=true} (Proof_Context.theory_of lthy) (ProgramInfo.get_csenv prog_info)
        |> Typset.make
  val _ = tracing ("union_variants: " ^ @{make_string} union_variants)
  val all = Typset.union
    (Typset.union_sets (word_typs :: map process (Symtab.keys fn_infos)))
    (Typset.map map_heap_type addressableTs)
  val all_but_union_variants = Typset.subtract union_variants all

  (* the array elements of an addressable array need to be addressable *)
  val addressable_fields = addressable_fields @
    ( addressableTs
      |> Typset.filter
        (fn T => TermsTypes.is_array_type T andalso forall (fn (T', _) => T <> T') addressable_fields)
      |> Typset.dest
      |> map (fn T =>
              (T, {addressable = [[("", TermsTypes.element_type T)]], not_addressable = []})) )

  val types = addressable_fields |>
    map (fn (T, {addressable = addrs, not_addressable = na}) =>
        (T, addrs,
          if null na
            then All_Addressable (map the_single addrs)
            else Some_Addressable addrs))

  val ordered_Ts =
    let
      val all_Ts = map #1 types
      fun node (T, addrs, kind) =
        ((T, kind), map (snd o hd o rev) addrs |> filter (member (op =) all_Ts) |> sort_distinct Term_Ord.typ_ord)
      val graph = Typ_Graph.make (map node types)
      fun with_kind T = (T, Typ_Graph.get_node graph T)
    in
     graph |> Typ_Graph.topological_order |> rev |> map with_kind
      (* Note that array types naturally come before their element types in the resulting list,
        because of Term_Ord.typ_ord + rev *)
    end

  val atomic_Ts = all_but_union_variants
    |> Typset.subtract (Typset.make (map fst addressable_fields))
    |> Typset.dest

  val _ = Utils.verbose_msg 3 lthy (fn _ => "all: " ^ @{make_string} types)
  val _ = Utils.verbose_msg 3 lthy (fn _ => "virtual heaps: " ^ @{make_string} ordered_Ts)
  val _ = Utils.verbose_msg 3 lthy (fn _ => "atomic heaps: " ^ @{make_string} atomic_Ts)

in
  ((atomic_Ts, ordered_Ts), addressable_fields)
end

(* Get fields from the globals type that should be copied from the
 * old globals type to the new globals type. *)
fun get_real_global_vars globalsT thy =
  (* Get all existing globals, filtering out "t_hrs_'". *)
   Record.get_recT_fields thy globalsT
   |> fst
   |> filter (fn (a, _) => Long_Name.base_name a <> "t_hrs_'")

(* Get the "t_hrs_'" accessor from the given globals record type. *)
fun get_globals_t_hrs globalsT thy =
   Record.get_recT_fields thy globalsT
   |> fst
   |> filter (fn (a, _) => Long_Name.base_name a = "t_hrs_'")
   |> hd

fun field_selectors_from_path path =
  path
  |> map fst |> map (Long_Name.base_name)
  |> map (HOLogic.mk_string)
  |> HOLogic.mk_list HOLogic.stringT

fun mk_deref p (T, path) =
  let
    val rangeT = typ_of_path path
    val selectors = field_selectors_from_path path
  in
   \<^instantiate>\<open>'a = T and 'b = rangeT and p = \<open>Free (p, Utils.mk_ptrT T)\<close> and f = selectors
     in term \<open>PTR ('b) (&(p\<rightarrow>f))\<close> for p::\<open>'a::c_type ptr\<close>\<close>
  end

datatype heap_locale_kind = Typ | Private_Field | Array_1 | Array_2

fun select_tactic tactics N = fn i => nth (tactics N) (i - 1) i

infix 1 THEN_ALL_NEW_N;

(*Apply second tactic to all subgoals emerging from the first --
  provide the total number of emerged subgoals to the second tactic (as first argument) --
  following usual convention for subgoal-based tactics.*)
fun (tac1 THEN_ALL_NEW_N tac2) i st =
  st |> (tac1 i THEN (fn st' =>
    let
      val N = Thm.nprems_of st' - Thm.nprems_of st
    in st' |> Seq.INTERVAL (tac2 N) i (i + N) end));


fun get_interpretation ctxt prop =
  Goal.prove ctxt [] [] prop (fn {context, ...} =>
    DETERM (Locale.intro_locales_tac {strict = false, eager = true} context []))
  handle ERROR msg =>
    error ("No interpretation found (" ^ Syntax.string_of_term ctxt prop ^ ") error: " ^ msg)

fun check_interpretation ctxt prop =
  try (Goal.prove ctxt [] [] prop) (fn {context, ...} =>
        DETERM (Locale.intro_locales_tac {strict = false, eager = true} context []))

(* Generate "typ_heap_simulation" predicates for each heap type we have. *)
fun gen_mk_typ_heap_simulation_thm prog_info (heap_info:heap_info)
      getter setter valid heap_typing heap_typing_update open_types_T
      typ_name typ lthy =
  let
    val st =  #lift_fn_full heap_info
    val t_hrs = ProgramInfo.get_t_hrs_getter prog_info
    val t_hrs_update = ProgramInfo.get_t_hrs_setter prog_info

    val res_thms =
      if TermsTypes.is_array_type typ then [] else
             let
        val prop = lthy
          |> \<^infer_instantiate>\<open>st and getter and setter and valid and t_hrs and t_hrs_update
            in prop \<open>typ_heap_simulation st getter setter valid t_hrs t_hrs_update\<close> for valid\<close>
             in
      case check_interpretation lthy prop of
          SOME thm => [thm]
        | NONE => error "no typ_heap_simulation instance found"
      end
    val lthy =
      let
        val loc = @{locale stack_simulation_heap_typing}
        val _ = Utils.verbose_msg 0 lthy (fn _ => "Proving interpretation " ^ quote loc ^ " for " ^ quote typ_name)
        val simps = [#lift_fn_thm heap_info, @{thm hrs_htd_update}] @
          Named_Theorems.get lthy @{named_theorems stack_the_default_plift}
      in
        lthy
        |> interpret {
            locale = loc,
            qualifier = typ_name,
            qualifier_mandatory = true,
            params = [st, getter, setter, t_hrs, t_hrs_update, heap_typing, heap_typing_update,
              HP_TermsTypes.S lthy, open_types_T]
          }
          (fn ctxt =>
            match_tac ctxt @{thms typ_heap_simulation_open_types.stack_simulation_heap_typingI} 1 THEN
            DETERM (Locale.intro_locales_tac {strict = false, eager = true} ctxt []) THEN
            ALLGOALS (asm_full_simp_tac (ctxt addsimps simps)))
      end

  in
    (res_thms, lthy)
  end

fun interpret_hrs_lense prog_info thy =
  let
    val t_hrs = ProgramInfo.get_t_hrs_getter prog_info
    val t_hrs_update = ProgramInfo.get_t_hrs_setter prog_info

    val lthy = Named_Target.theory_init thy
    val hrs_tac = asm_full_simp_tac
    fun lense_solver ctxt i =
        Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN
        SOLVED_DETERM_verbose "t_hrs_get_upd:" ctxt (hrs_tac ctxt) i THEN
        SOLVED_DETERM_verbose "t_hrs_upd_same:" ctxt (hrs_tac ctxt) i THEN
        SOLVED_DETERM_verbose "t_hrs_upd_compose:" ctxt (hrs_tac ctxt) i

    val prop = \<^infer_instantiate>\<open>t_hrs and t_hrs_update in prop \<open>lense t_hrs t_hrs_update\<close>\<close> lthy
      |> (fn prop => Goal.prove_future lthy [] [] prop (fn {context, ...} =>
            (lense_solver context 1)))
    val thy = lthy
      |> interpret {
          locale = @{locale "lense"},
          qualifier = "heap",
          qualifier_mandatory = true,
          params = [t_hrs, t_hrs_update] }
        (fn ctxt => resolve_tac ctxt [prop] 1)
      |> Local_Theory.exit_global
  in
    thy
  end

(* Generate "typ_heap_simulation" predicates for each heap type we have. *)
fun mk_typ_heap_simulation_thm prog_info (heap_info : heap_info) typ lthy =
  let
    val heap_tab = #heap_tab heap_info
    val {getter, setter, ...} = Typtab.lookup heap_tab typ |> the
    val heap_typing = #heap_typing heap_info
    val T = typ
    val ptr_valid = AList.lookup (op =) (#ptr_valids heap_info) T |> the |> #1
    val valid = \<^infer_instantiate>\<open>ptr_valid = ptr_valid and heap_typing=heap_typing
           in term \<open>\<lambda>s. ptr_valid (heap_typing s)\<close>\<close> lthy
    val typ_name = name_from_type T
    val heap_typing = #heap_typing heap_info
    val heap_typing_update = #heap_typing_update heap_info
    val open_types_T = #open_types_T heap_info
  in
    gen_mk_typ_heap_simulation_thm prog_info heap_info getter setter valid
      heap_typing heap_typing_update open_types_T typ_name typ lthy
  end


(* Generate lifted_globals lemmas and instantiate them into the heap lifting rules. *)
fun lifted_globals_lemmas prog_info heap_info lthy = let
  (* Tactic to solve subgoals below. *)
  local
    (* Fetch simp rules generated by the C Parser about structures. *)
    val struct_simpset = Named_Theorems.get lthy
    val struct_simps =
        (struct_simpset @{named_theorems "typ_name_simps"})
        @ (struct_simpset @{named_theorems "typ_name_itself"})
        @ (struct_simpset @{named_theorems "fl_ti_simps"})
        @ (struct_simpset @{named_theorems "fl_Some_simps"})
        @ (struct_simpset @{named_theorems "fg_cons_simps"})
    val base_ss = simpset_of @{theory_context HeapLift}
    val record_ss = RecordUtils.get_record_simpset lthy
    val merged_ss = merge_ss (base_ss, record_ss)

    (* Generate a simpset containing everything we need. *)
    val ss =
      (Context_Position.set_visible false lthy)
      |> put_simpset merged_ss
      |> (fn ctxt => ctxt
                addsimps [#lift_fn_thm heap_info]
                    @ @{thms typ_simple_heap_simps}
                    @ @{thms valid_globals_field_def}
                    @ @{thms the_fun_upd_lemmas export_tag_adjust_ti}
                    @ struct_simps)
      |> simpset_of
  in
    fun subgoal_solver_tac ctxt =
      (fast_force_tac (put_simpset ss ctxt) 1)
        ORELSE (CHANGED (Method.try_intros_tac ctxt [@{thm conjI}, @{thm ext}] []
            THEN clarsimp_tac (put_simpset ss ctxt) 1))
  end

  (* Make thms for all types. *)
  val all_heap_types = #heap_types heap_info

  val (typ_heap_simulation_thmss, lthy) = lthy |> fold_map (mk_typ_heap_simulation_thm prog_info heap_info) all_heap_types

  val typ_heap_simulation_thms = flat typ_heap_simulation_thmss
  (* Generate "typ_heap_simulation" thms for signed words. *)
  val typ_heap_simulation_thms =
      typ_heap_simulation_thms
      @ (map_product
            (fn a => fn b => try (fn _ => a OF [b]) ())
            @{thms signed_typ_heap_simulations}
            typ_heap_simulation_thms
        |> map_filter I)

  (* Generate "valid_struct_field" for each field of each struct. *)
  fun mk_valid_struct_field_thm struct_name _ (field_info : field_info) =
    \<^infer_instantiate>\<open>fname = \<open>Utils.encode_isa_string (#name field_info)\<close> and fgetter = \<open>#getter field_info\<close> and
        fsetter = \<open>#setter field_info\<close> and t_hrs = \<open>ProgramInfo.get_t_hrs_getter prog_info\<close> and
        t_hrs_update = \<open>ProgramInfo.get_t_hrs_setter prog_info\<close>
      in prop \<open>valid_struct_field [fname] fgetter fsetter t_hrs t_hrs_update\<close>\<close> lthy
    |> (fn prop =>
         (* HACK: valid_struct_field currently works only for packed types,
          * so typecheck the prop first *)
         case try (Syntax.check_term lthy) prop of
           SOME _ =>
             [Goal.prove_future lthy [] [] prop
                (fn params =>
                   (resolve_tac lthy @{thms valid_struct_fieldI} 1) THEN
                   (* Need some extra thms from the records package for our struct type. *)
                   (EqSubst.eqsubst_tac lthy [0]
                      [hd (Proof_Context.get_thms lthy (struct_name ^ "_idupdates")) RS @{thm sym}] 1
                      THEN asm_full_simp_tac lthy 1) THEN
                   (FIRST (Proof_Context.get_thms lthy (struct_name ^ "_fold_congs")
                           |> map (fn t => resolve_tac lthy [t OF @{thms refl refl}] 1))
                      THEN asm_full_simp_tac lthy 1) THEN
                   (REPEAT (subgoal_solver_tac (#context params))))]
           | NONE => [])

  (* Make thms for all fields of structs in our heap. *)
  fun valid_struct_abs_thms T =
    case (Typtab.lookup (#struct_types heap_info) T) of
      NONE => []
    | SOME struct_info =>
        map (fn field =>
                  mk_valid_struct_field_thm (#name struct_info) T field)
            (#field_info struct_info)
        |> List.concat
  val valid_field_thms = map valid_struct_abs_thms all_heap_types |> List.concat

  (* Generate conversions from globals embedded directly in the "globals" and
   * "lifted_globals" record. *)
  fun mk_valid_globals_field_thm name =
    \<^infer_instantiate>\<open>st = \<open>#lift_fn_full heap_info\<close> and
      old_get = \<open>Symtab.lookup (#global_field_getters heap_info) name |> the |> fst\<close> and
      old_set = \<open>Symtab.lookup (#global_field_setters heap_info) name |> the |> fst\<close> and
      new_get = \<open>Symtab.lookup (#global_field_getters heap_info) name |> the |> snd\<close> and
      new_set = \<open>Symtab.lookup (#global_field_setters heap_info) name |> the |> snd\<close>
    in prop \<open>valid_globals_field st old_get old_set new_get new_set\<close>\<close> lthy
    |> (fn prop => Goal.prove_future lthy [] [] prop (fn params => subgoal_solver_tac (#context params)))
  val valid_global_field_thms = map (#1 #> mk_valid_globals_field_thm) (#global_fields heap_info)
  (* At this point, the lemmas are ready to be instantiated into the generic
   * heap_abs rules (which will be fetched from the most recent lthy). *)

in
  ([ typ_heap_simulation_thms, valid_field_thms, valid_global_field_thms ], lthy)
end;

fun note binding attrs thms lthy =
  lthy |> Local_Theory.note ((binding, attrs), thms) |> snd

fun heap_array (stateT, eT, iT) = Sign.mk_const @{theory}
  (@{const_name pointer_array_lense.heap_array}, [stateT, eT, iT])

fun heap_array_map (stateT, eT, iT) = Sign.mk_const @{theory}
  (@{const_name pointer_array_lense.heap_array_map}, [stateT, eT, iT])

fun valid_array (stateT, eT, iT) = Sign.mk_const @{theory}
  (@{const_name valid_array_base.valid_array}, [stateT, eT, iT])

fun stateT_from_getter t = fastype_of t |> strip_type |> fst |> hd
fun elT_from_valid t = fastype_of t |> strip_type |> fst |> (fn xs => nth xs 1) |> TermsTypes.dest_ptr_ty

fun indexT 1 = @{typ "'i::array_max_count"}
  | indexT 2 = @{typ "'j::array_max_count"}
  | indexT _ = error ("indexT: only supports two dimensions")

fun ptr_valid_heap_typing ptr_valid heap_typing ctxt T =
  \<^infer_instantiate>\<open>ptr_valid = \<open>ptr_valid T\<close> and heap_typing=heap_typing
           in term \<open>\<lambda>s. ptr_valid (heap_typing s)\<close>\<close> ctxt

fun gen_lookup_valid generalise_index_type depth ptr_valid heap_typing ctxt T =
      (case try TermsTypes.dest_array_type T of
         SOME (eT, iT) => gen_lookup_valid generalise_index_type (depth + 1) ptr_valid heap_typing ctxt eT
           |> Option.map (fn valid =>
               let
                 val iT' = if generalise_index_type then indexT (2 - depth) else iT
                 val sT = stateT_from_getter valid
                 val eT' = elT_from_valid valid
               in valid_array (sT, eT', iT') $ valid end)
       | NONE => SOME (ptr_valid_heap_typing ptr_valid heap_typing ctxt T))

val lookup_valid = gen_lookup_valid false 0

fun interprete_pointer_array_lense_with_loc loc typ getter setter =
  interpret {
    locale = loc,
    qualifier = name_with_signed_from_type typ,
    qualifier_mandatory = true,
    params = [getter, setter] }
  (fn ctxt => Locale.intro_locales_tac {strict = false, eager = true} ctxt [])

fun interprete_pointer_array_lense typ getter setter lthy =
  if Sign.of_sort (Proof_Context.theory_of lthy) (typ, @{sort "array_inner_max_size"}) then
    interprete_pointer_array_lense_with_loc @{locale pointer_two_dimensional_array_lense} typ getter setter lthy
  else if Sign.of_sort (Proof_Context.theory_of lthy) (typ, @{sort "array_outer_max_size"}) then
    interprete_pointer_array_lense_with_loc @{locale pointer_array_lense} typ getter setter lthy
  else lthy

fun ptr_valid_instance_tac ctxt =
  let
    val ctxt = ctxt delsimps @{thms field_lookup_offset_untyped_eq size_simps size_align_simps}
    val ptr_valid_def = Named_Theorems.get ctxt @{named_theorems ptr_valid_definition}
    val ptr_valid_u_recursion = Named_Theorems.get ctxt @{named_theorems ptr_valid_u_recursion}
    val fold_ptr_valid = Named_Theorems.get ctxt @{named_theorems fold_ptr_valid}
  in
    simp_tac (ctxt addsimps ptr_valid_def) 1 THEN
    EqSubst.eqsubst_tac ctxt [0] ptr_valid_u_recursion 1 THEN
    asm_full_simp_tac (Raw_Simplifier.add_cong @{thm HOL.conj_cong} ctxt) 1 THEN
    simp_tac (ctxt addsimps (fold_ptr_valid @
       @{thms fold_root_ptr_valid_u fold_field_lvalue Bex_intvl_conv Bex_union_conv})) 1 THEN
    REPEAT (EqSubst.eqsubst_tac ctxt [0] @{thms fold_exists_ptr} 1)
  end

fun ptr_valid_instance ctxt ptr_valid T =
  let
    val ([d, p], ctxt') = Utils.fix_variant_frees [("d", @{typ heap_typ_desc}), ("p",\<^Type>\<open>ptr T\<close>)] ctxt
    val ptr_valid = \<^instantiate>\<open>'a=\<open>T\<close> and ptr_valid = \<open>ptr_valid T\<close> and d=d and p=p in
          term \<open>ptr_valid d p::bool\<close> for d::heap_typ_desc and p::"'a::mem_type ptr"\<close>
      |> Thm.cterm_of ctxt'
    val [eq_thm] = eq_by_tac ptr_valid_instance_tac ctxt' ptr_valid |> single |> Proof_Context.export ctxt' ctxt
  in
    eq_thm
  end

fun mk_cases ctxt ptr_valid_eq =
  let
    val ([P], ctxt') = Utils.fix_variant_cfrees [("P", @{typ bool})] ctxt
    val cases_raw = \<^instantiate>\<open>valid = \<open>Utils.clhs_of_eq (Thm.cprop_of (ptr_valid_eq))\<close> and P=P in
          lemma \<open>valid \<Longrightarrow> (valid \<Longrightarrow> P) \<Longrightarrow> P\<close> for valid P::bool by blast\<close>
    val cases = cases_raw
      |> Tactic.rule_by_tactic ctxt (2 |> (
           EqSubst.eqsubst_asm_tac ctxt [0] [ptr_valid_eq] THEN_ALL_NEW
           TRY' (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms disjE conjE exE}))))
      |> singleton (Proof_Context.export ctxt' ctxt)
      |> Drule.zero_var_indexes
    fun typ_name @{term_pat \<open>Trueprop (?valid _ ?p)\<close>} = p
      |> fastype_of |> \<^Type_fn>\<open>ptr T => \<open>T\<close>\<close>
      |> name_from_type

    val case_names = cases |> Thm.prems_of |> tl
      |> map (map_filter (try typ_name) o fst o Logic.strip_horn o snd o Utils.strip_all)
      |> flat
  in
    (cases, case_names)
  end

fun note_ptr_valid_thms ptr_valid Ts lthy =
  let
    val eqs = map (ptr_valid_instance lthy ptr_valid) Ts
    val cases = map (mk_cases lthy) eqs
    fun note (T, (eq, (cases, case_names))) lthy =
      let
        val name = name_from_type T
        val unfoldB = \<^binding>\<open>unfold\<close> |> Binding.qualify true "ptr_valid" |> Binding.qualify true name
        val casesB = \<^binding>\<open>cases\<close> |> Binding.qualify true "ptr_valid" |> Binding.qualify true name

        val case_attrs = @{attributes [consumes 1]} @ [(Attrib.internal \<^here> (K (Rule_Cases.case_names case_names)))]
        val ((_, [eq]), ((_, [cases]), lthy)) = lthy
          |> Local_Theory.note ((unfoldB, @{attributes [ptr_valid]}), [eq])
          ||> Local_Theory.note ((casesB, case_attrs), [cases])
      in
        ((T, (ptr_valid T, eq, cases)), lthy)
      end

    val (ptr_valids, lthy) = lthy |> fold_map note (Ts ~~ (eqs ~~ cases))
  in
    (ptr_valids, lthy)
  end

(*
 * Define a new heap record using the record package.
 *
 * "globalsT" is the type of the existing globals record, while "heapTs" is a
 * list of the different types the new heap will need to support.
 *)
fun gen_new_heap prog_info addressable_fields make_lifted_globals_field_name globalsT
  (atomicTs : typ list, orderedTs : (typ * addressable_kind) list) thy =
let
  (* N.B. there is an overloading of the nomenclature "field" in the code meaning either
   * a field of the globals record, or a field of a struct
   *)

  val heapTs = map (rpair None_Addressable) atomicTs @ orderedTs

  val existing_fields = get_real_global_vars globalsT thy

  (* Generate new fields. *)
  val new_names = existing_fields |>
     map (make_lifted_globals_field_name o unsuffix "_'" o Long_Name.base_name o fst)

  val copied_fields = existing_fields ~~ new_names |>
     map (fn ((_, ty), new_name) => (Binding.name new_name, ty, NoSyn))

  val heap_fields = heapTs |>
    map_filter (fn
        (_, All_Addressable _) => NONE
      | (T, Some_Addressable _) =>
          SOME (Binding.name ("dedicated_heap_" ^ name_from_type T), Utils.mk_ptrT T --> T, NoSyn)
      | (T, None_Addressable) =>
          SOME (Binding.name ("heap_" ^ name_from_type T), Utils.mk_ptrT T --> T, NoSyn))

  val heap_typing =
     (Binding.name AC_Names.heap_typingN, @{typ heap_typ_desc}, NoSyn)

  (* global_interpretation lense t_hrs_' t_hrs_'_update *)
  val thy = thy |> interpret_hrs_lense prog_info

  val valid_heapTks_no_array = heapTs |> filter_out (fn (T, _) => TermsTypes.is_array_type T)

  (* Define the record. *)
  val thy = Record.add_record {overloaded = false} ([], Binding.name AC_Names.new_heap_recN)
    NONE (copied_fields @ heap_fields @ [heap_typing]) thy

  (* The record package doesn't tell us what we just defined, so we
   * attempt to fetch the type of the record. *)
  val full_rec_name = Sign.full_name thy (Binding.name AC_Names.new_heap_recN)
  val lifted_globals_infos = Record.the_info thy full_rec_name
  val lifted_globals_equality = #equality lifted_globals_infos
  val lifted_globalsT = Proof_Context.read_typ (Proof_Context.init_global thy) full_rec_name

  (* Create a list of the names of the new fields. *)
  val new_fields = Record.get_extT_fields thy lifted_globalsT |> fst
  val new_copied_fields = take (length copied_fields) new_fields

  val all_fields = new_fields |> map (fn (f, T) =>
         (Const (f, lifted_globalsT --> T),
          Const (f ^  Record.updateN, (T --> T) --> lifted_globalsT --> lifted_globalsT)))

  val (all_fields_wo_typing, (heap_typing, heap_typing_update)) = split_last all_fields

  (* Hide the constants of existing fields, if required. *)
  val overlapped_names = filter (fn n => member op= new_names (Long_Name.base_name n)) (map fst existing_fields)
  val thy = fold (Sign.hide_const false) overlapped_names thy

  (* Generate a mapping from heap types to the getter/setter for that heap. *)
  val heap_fields =
      Record.get_recT_fields thy lifted_globalsT |> fst
      |> drop (length copied_fields)
      |> take (length heap_fields)

  val getters = map (fn (a,b) => (a, lifted_globalsT --> b)) heap_fields
  val setters = map (fn (a,b) => (a ^ Record.updateN, (b --> b) --> (lifted_globalsT --> lifted_globalsT))) heap_fields

  val lthy = Named_Target.theory_init thy

  val _ = Utils.verbose_msg 0 lthy (fn _ => Record.string_of_record lthy AC_Names.new_heap_recN)

  fun typ_uinfo_t T = \<^instantiate>\<open>'a=T in term \<open>typ_uinfo_t TYPE('a::c_type)\<close>\<close>
  fun indexes n = \<^instantiate>\<open>n=\<open>HOLogic.mk_number @{typ nat} n\<close> in term \<open>array_fields n\<close>\<close>

  val record_thy = Proof_Context.theory_of lthy
  val record_info = RecursiveRecordPackage.get_info record_thy

  (* create lift_global_heap *)
  val _ = Utils.verbose_msg 0 lthy (fn _ => "Construct lift_global_heap")
  val dummy_old_globals = Free ("g", globalsT)

  (* Fetch the fields of the globals record. *)
  val existing_fields = get_real_global_vars globalsT record_thy

  (* Fetch the "t_hrs_'" variable from the old globals, which
   * contains heap data. *)
  val t_hrs = get_globals_t_hrs globalsT record_thy
  val t_hrs = Const (fst t_hrs, fastype_of dummy_old_globals --> snd t_hrs)

  (* create open_types *)
  val _ = Utils.verbose_msg 0 lthy (fn _ => "Construct open_types")

  fun open_type (T, {addressable, not_addressable}) =
    let
      fun open_array_type T =
        case try TermsTypes.dest_array_index T of
          SOME (eT, n) => (typ_uinfo_t T, indexes n)::open_array_type eT
        | NONE => []

      val record_info = Symtab.lookup record_info (dest_Type T |> fst)
      val fields =
        (if null not_addressable andalso is_some record_info then
          record_info |> the |> #fields |> map single
        else
          addressable)
        |> map (HOLogic.mk_list @{typ string} o map (HOLogic.mk_string o Long_Name.base_name o fst))
        |> HOLogic.mk_list @{typ "string list"}
    in
      if TermsTypes.is_array_type T then
        open_array_type T
      else
        [(typ_uinfo_t T, fields)]
    end

  val open_types = addressable_fields |> map open_type |> flat
    |> map HOLogic.mk_prod
    |> HOLogic.mk_list @{typ "(typ_uinfo * qualified_field_name list)"}

  val ((open_types_T, def_thm), lthy) = lthy |>
          Utils.define_global_const \<^binding>\<open>\<T>\<close> false open_types [] @{attributes [\<T>_def]}

  val prog_name = ProgramInfo.get_prog_name prog_info
  val _ = Utils.verbose_msg 0 lthy (fn _ => "Proving interpretation " ^ quote @{locale open_types} ^
           " for:\n " ^ (Thm.string_of_thm lthy def_thm))
  val lthy = lthy
    |> interpret {
        locale = @{locale open_types},
        qualifier = prog_name,
        qualifier_mandatory = false,
        params = [open_types_T] }
      (fn ctxt =>
        resolve_tac ctxt @{thms open_types.intro} 1 THEN
        force_tac (ctxt addsimps [def_thm]) 1 THEN
        auto_tac (ctxt addsimps [def_thm]))

   val _ = Utils.verbose_msg 0 lthy (fn _ => "Proving interpretation " ^ quote @{locale open_types_heap_typing_state} ^
           " for:\n " ^ (Thm.string_of_thm lthy def_thm) ^ ", " 
                      ^ Syntax.string_of_term lthy heap_typing ^ ", " 
                      ^ Syntax.string_of_term lthy heap_typing_update)

   val lthy = lthy
    |> interpret {
        locale = @{locale open_types_heap_typing_state},
        qualifier = AC_Names.new_heap_recN,
        qualifier_mandatory = false,
        params = [open_types_T, heap_typing, heap_typing_update] }
      (fn ctxt =>
        DETERM (Locale.intro_locales_tac {strict = false, eager = true} ctxt []) THEN
        auto_tac ctxt)
    |> AutoCorresData.in_theory Cached_Theory_Simproc.init_thy

  val (_, lthy) =
    let
      val list_ex_T_thm = @{thm list_ex_subst_def} OF [def_thm]
    in
      lthy
      |> Utils.timeap_msg 0 lthy (fn _ => "Add list_ex_\<T> thm")
        (Local_Theory.note ((\<^binding>\<open>list_ex_\<T>\<close>, @{attributes [simp]}), [list_ex_T_thm]))
    end

  val ptr_valid_poly = Syntax.read_term lthy (Long_Name.qualify prog_name (Long_Name.base_name @{const_name open_types.ptr_valid}))
  fun ptr_valid T = Term_Subst.instantiate_frees (TFrees.make [(("'a", @{sort mem_type}), T)], Frees.empty) ptr_valid_poly
  val (ptr_valids, lthy) = lthy
    |> Utils.timeap_msg 0 lthy (fn _ => "Prove ptr_valid_...")
      (note_ptr_valid_thms ptr_valid (map fst heapTs))


  val _ = Utils.verbose_msg 0 lthy (fn _ => "Define valid_...")
  fun mk_valid T = lookup_valid ptr_valid heap_typing lthy T |> the

  fun define_is_valid (T, _) lthy =
    let
      val lhs = mk_valid T
      val valid_array_convs = Named_Theorems.get lthy @{named_theorems valid_array_conv}

      val prop = \<^infer_instantiate>\<open>heap_typing = heap_typing and is_valid = lhs in
            prop (schematic) \<open>heap_typing s = heap_typing s' \<Longrightarrow> is_valid s = is_valid s'\<close>\<close> lthy
      val valid_conv = autofix_prove_future lthy [] [] prop (fn {context, ...} =>
            asm_simp_tac (context addsimps (valid_array_convs @ @{thms fun_eq_iff})) 1)

      fun valid_upd other_upd =
        let
          val prop = \<^infer_instantiate>\<open>is_valid = lhs and upd = other_upd
            in prop (schematic) \<open>is_valid (upd f s) = is_valid s\<close>\<close> lthy
          val thm = autofix_prove_future lthy [] [] prop (fn {context, ...} =>
            resolve_tac context [valid_conv] 1 THEN
            asm_full_simp_tac context 1)
        in
          thm
        end
      val valid_upds = map (valid_upd o #2) all_fields_wo_typing
    in
      lthy
      |> note (Binding.make (name_from_type T ^ "_valid_conv", \<^here>)) @{attributes [valid_conv]} [valid_conv]
        |> note (Binding.make (name_from_type T ^ "_valid_update", \<^here>)) @{attributes [simp]} valid_upds
    end

  val lthy = lthy |> fold define_is_valid valid_heapTks_no_array
  val _ = Utils.verbose_msg 0 lthy (fn _ => "Exit global")

  fun lift_heap (T, _) =
    \<^infer_instantiate>\<open>'a = T and \<T> = \<open>open_types_T\<close> and t_hrs = t_hrs and s = dummy_old_globals
        in term \<open>\<lambda>p. open_types.read_dedicated_heap \<T> (t_hrs s) (p::('a::mem_type) ptr)\<close>\<close> lthy

  (*
   * We assume that the order of the variables in "lifted_globalsT"
   * match those in existing fields, followed by those in
   * heapTs.
   *
   * If this assumption is wrong, the following probably will
   * not type check (and, if it does, will be wrong).
   *
   * Our first step, we copy fields from the globals type.
   *)

  (* Next, we generate lifted heaps from the globals type. *)
  val lift_term =
    RecordUtils.get_record_constructor record_thy lifted_globalsT
    |> fold (fn (name, t) => fn rest =>
      (rest $ (Const (name, globalsT --> t) $ dummy_old_globals)))
        existing_fields
    |> fold (fn Tk => fn rest => rest $ lift_heap Tk)
         (filter_out (is_All_Addressable o snd) heapTs)
    |> (fn rest => rest $ (@{const hrs_htd} $ (t_hrs $ dummy_old_globals)))
    |> (fn t => t $ @{term "()"})
    |> Syntax.check_term lthy

  (* later code expects the global Const (not the local Free), so we export results here *)
  val ((lift, lift_def), lthy) =
    lthy
    |> Utils.define_global_const (Binding.make ("lift_global_heap", \<^here>)) false
        lift_term [("g", globalsT)] []

  val _ = Utils.verbose_msg 0 lthy (fn _ => Thm.string_of_thm lthy lift_def)
  (* Generate some simp rules to make life easier. *)
  (* FIXME: add to simpset ?*)
  val (lift_simp_thms, lthy) = RecordUtils.generate_ext_simps "lifted_globals_ext_simps" lift_def lthy

  val _ = Utils.verbose_msg 0 lthy (fn _ => "Prove heap_typing_simulation " ^
    string_of_typs lthy (map fst heapTs))
  val t_hrs = ProgramInfo.get_t_hrs_getter prog_info
  val t_hrs_update = ProgramInfo.get_t_hrs_setter prog_info
  val lthy = lthy
    |> interpret {
        locale = @{locale "heap_typing_simulation"},
        qualifier = AC_Names.new_heap_recN,
        qualifier_mandatory = false,
        params = [open_types_T, t_hrs, t_hrs_update, heap_typing, heap_typing_update, lift]
      }
      (fn ctxt =>
          Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN
        ALLGOALS (asm_full_simp_tac (ctxt addsimps [lift_def])))

  (* create getters / setters *)
  fun merge_heap_fields ((T, All_Addressable k)::Ts) hs =
      (T, (All_Addressable k, NONE)) :: merge_heap_fields Ts hs
    | merge_heap_fields ((T, Some_Addressable k)::Ts) (h :: hs) =
      (T, (Some_Addressable k, SOME h)) :: merge_heap_fields Ts hs
    | merge_heap_fields ((T, No_Addressable)::Ts) (h :: hs) =
      (T, (No_Addressable, SOME h)) :: merge_heap_fields Ts hs
    | merge_heap_fields _ _ = []

  fun typ_heap_simulation_open_types_params_stack r w v =
    [open_types_T, lift, r, w, v, t_hrs, t_hrs_update, heap_typing, heap_typing_update, HP_TermsTypes.S lthy]

  fun typ_heap_simulation_open_types_params r w v =
    [open_types_T, lift, r, w, v, t_hrs, t_hrs_update, heap_typing, heap_typing_update]

  val fold_congs = record_info
    |> Symtab.keys
    |> maps (fn name => name ^ "_fold_congs" |> Proof_Context.get_thms lthy)
    |> map (fn thm => thm OF @{thms refl refl})
  val fg_cons = Named_Theorems.get lthy @{named_theorems fg_cons_simps}
  val zero_simps = Named_Theorems.get lthy @{named_theorems zero_simps}

  fun typ_heap_simulation_of_field lthy (_, fget, fset, _, d) =
    let
      val thm = Drule.infer_instantiate' lthy (map (Option.map (Thm.cterm_of lthy))
        (map SOME (typ_heap_simulation_open_types_params (#hget d) (#hupd d) (#hvalid d)) @
          [NONE, SOME fget, SOME fset]))
        @{thm typ_heap_simulation_open_types.typ_heap_simulation_of_field}

      fun dest_fun_seq (Abs (_, _, f)) = dest_fun_seq f
        | dest_fun_seq (f $ x) = f :: dest_fun_seq x
        | dest_fun_seq (t as Const _) = [t]
        | dest_fun_seq _ = []

      val gs_us = (dest_fun_seq fget |> rev) ~~ (dest_fun_seq fset)

      fun field_with_lense_tac ((g, u)::gs_us) ctxt =
        let
          val thm = Drule.infer_instantiate' lthy (map (Option.map (Thm.cterm_of lthy))
            [NONE, NONE, NONE, NONE, SOME g, SOME u])
            @{thm field_with_lense_Cons}
        in
          resolve_tac ctxt [thm] THEN'
          field_with_lense_tac gs_us ctxt THEN'
          SOLVED' (asm_full_simp_tac ctxt) THEN'
          SOLVED' (match_tac ctxt fg_cons) THEN'
          SOLVED' (match_tac ctxt fold_congs THEN' asm_full_simp_tac ctxt)
        end
        | field_with_lense_tac [] ctxt = match_tac ctxt @{thms field_with_lense_Nil}

    in
      SELECT_GOAL ((
        match_tac lthy [thm] THEN'
        SELECT_GOAL (DETERM (Locale.intro_locales_tac {strict = true, eager = false} lthy [])) THEN'
        SOLVED' (field_with_lense_tac gs_us lthy) THEN'
        SOLVED' (K (ALLGOALS (asm_full_simp_tac (lthy addsimps (@{thms comp_def} @ zero_simps)))))) 1)
    end

  fun typ_heap_simulation T getter setter valid tac lthy =
    lthy
    |> interpret {
        locale = @{locale "typ_heap_simulation_open_types_stack"},
        qualifier = "heap_" ^ name_with_signed_from_type T,
        qualifier_mandatory = true,
        params = typ_heap_simulation_open_types_params_stack getter setter valid }
      (fn ctxt => resolve_tac ctxt @{thms typ_heap_simulation_open_types_stack.intro} 1 THEN tac ctxt)
    |> interprete_pointer_array_lense T getter setter

  fun heap_field_disj (fields : heap_field_info list) setter init pointer_disj_thm comp_disj_thm lthy =
    let
      val atomic_upds = (fields, Ord_List.make Term_Ord.fast_term_ord init)
        |-> fold (fn d => fn Ts => Ord_List.union Term_Ord.fast_term_ord Ts (#atomic_upds d))

      fun pointer_writer_disjnt lthy =
        let
          val alpha = TFree ("'a", @{sort mem_type})
          val w = Free ("w", Type (@{type_name ptr}, [alpha]) --> lifted_globalsT --> lifted_globalsT)
          val prems = map (fn upd =>
            \<^infer_instantiate>\<open>'a=\<open>alpha\<close> and 's=\<open>lifted_globalsT\<close> and upd = \<open>upd\<close> and w = \<open>w\<close> in
              prop \<open>\<And>f. pointer_writer_disjnt (\<lambda>p. upd p f) w\<close>
              for w :: "'a::mem_type ptr \<Rightarrow> 's upd"\<close> lthy
            ) atomic_upds
          val disj_thm = Goal.prove lthy ["w"] prems
            (\<^infer_instantiate>\<open> upd = \<open>setter\<close> and w = \<open>w\<close> in
                prop \<open>\<And>f. pointer_writer_disjnt (\<lambda>p. upd p f) w\<close>\<close> lthy)
            (fn { context, prems } =>
                ( match_tac context [Object_Logic.rulify context pointer_disj_thm] THEN_ALL_NEW
                  REPEAT_ALL_NEW (
                    match_tac context (@{thms allI list_all_cons list_all_nil pointer_writer_disjnt_ptr_left
                      pointer_writer_disjnt_ptr_corce_signed} @
                      prems @
                      Named_Theorems.get context @{named_theorems pointer_writer_disjnt_intros}) ORELSE'
                    SOLVED' (asm_full_simp_tac context))) 1)
        in
          note Binding.empty @{attributes [pointer_writer_disjnt_intros]}
            ([disj_thm, @{thm pointer_writer_disjnt_sym} OF [disj_thm]]) lthy
        end

      fun comp_writer_disjnt lthy =
        let
          val w = Free ("w", lifted_globalsT --> lifted_globalsT)
          val prems = map (fn upd =>
            \<^infer_instantiate>\<open>'s=\<open>lifted_globalsT\<close> and upd = \<open>upd\<close> and w = \<open>w\<close> in
              prop \<open>\<And>p x. upd p x o w = w o upd p x\<close>
              for upd :: "'a::mem_type ptr \<Rightarrow> 'a upd \<Rightarrow> 's upd" and p\<close> lthy
            ) atomic_upds
          val disj_thm = Goal.prove lthy ["w"] prems
            (\<^infer_instantiate>\<open> upd = \<open>setter\<close> and w = \<open>w\<close> in
                prop \<open>\<And>p f. upd p f o w = w o upd p f\<close>\<close> lthy)
            (fn { context, prems } =>
                ( match_tac context [Object_Logic.rulify context comp_disj_thm] THEN_ALL_NEW
                  REPEAT_ALL_NEW (
                    match_tac context (@{thms allI list_all_cons list_all_nil} @
                      prems @
                      Named_Theorems.get context @{named_theorems disjnt_heap_fields_comp}) ORELSE'
                    SOLVED' (asm_full_simp_tac (context addsimps @{thms fun_eq_iff})))) 1)
        in
          note Binding.empty @{attributes [disjnt_heap_fields_comp]} ([disj_thm]) lthy
        end

      in
        lthy
        |> Config.put Record.sort_updates true
        |> pointer_writer_disjnt
        |> comp_writer_disjnt
        |> (fn lthy => (atomic_upds, lthy))
      end

  fun construct_array_heap T (tab : heap_field_info Typtab.table) lthy =
    let
      val (eT, iT) = TermsTypes.dest_array_type T
      val (data, (tab, lthy)) = case Typtab.lookup tab eT of
          SOME data => (data, (tab, lthy))
        | NONE => if TermsTypes.is_array_type eT then
          let
            val (tab, lthy) = construct_array_heap eT tab lthy
          in
            (Typtab.lookup tab eT |> the, (tab, lthy))
          end
          else error "type not found in heap table"
    in Utils.timeit_msg 0 lthy
      (fn _ => "Construct typ simulation for " ^ Syntax.string_of_typ lthy T ^ " (array)")
      (fn _ => let
        val hget = heap_array (lifted_globalsT, eT, iT) $ #hget data
        val hupd = heap_array_map (lifted_globalsT, eT, iT) $ #hget data $ #hupd data
        val hvalid = valid_array (lifted_globalsT, eT, iT) $ #hvalid data
        val lthy = lthy
          |> typ_heap_simulation T hget hupd hvalid
            (fn ctxt =>
              match_tac ctxt [@{thm array_typ_heap_simulation_of_typ_heap_simulation}] 1 THEN
              Locale.intro_locales_tac {strict = false, eager = true} ctxt [] THEN
              asm_simp_tac ctxt 1)
        val array_data = {
          hget = hget,
          hupd = hupd,
          hvalid = hvalid,
          atomic_upds = #atomic_upds data,
          pointer_lense_axiom =
            get_interpretation lthy (\<^infer_instantiate>\<open>g = hget and u = hupd in
                prop \<open>pointer_lense g u\<close>\<close> lthy) }
      in
        (Typtab.update_new (T, array_data) tab, lthy)
      end)
    end

  fun construct_signed_heap T (tab : heap_field_info Typtab.table) lthy =
    let
      val data = Typtab.lookup tab T |> the
      val (_, [aT]) = dest_Type T
      val sT = Type (@{type_name Word.word}, [Type (@{type_name Signed_Words.signed}, [aT])])
    in Utils.timeit_msg 0 lthy
      (fn _ => "Construct typ simulation for " ^ Syntax.string_of_typ lthy sT)
      (fn _ => let
        val hget = \<^infer_instantiate>\<open>r = "#hget data" and 'a=aT in term \<open>signed_heap (r::('s \<Rightarrow> 'a::len word ptr \<Rightarrow> 'a word))\<close>\<close> lthy
        val hupd = \<^infer_instantiate>\<open>w = "#hupd data" and 'a=aT in term \<open>\<lambda>p m.
            w (PTR_COERCE('a::len signed word \<rightarrow> 'a word) p)
              (\<lambda>w. UCAST('a signed \<rightarrow> 'a) (m (UCAST('a \<rightarrow> 'a signed) w)))\<close>\<close> lthy
        val hvalid = \<^infer_instantiate>\<open>v = "#hvalid data" and 'a=aT in term \<open>\<lambda>h p.
            v h (PTR_COERCE('a::len signed word \<rightarrow> 'a word) p)\<close>\<close> lthy

        val lthy = lthy
          |> typ_heap_simulation sT hget hupd hvalid
            (fn ctxt =>
              match_tac ctxt [@{thm signed_typ_heap_simulation_of_typ_heap_simulation}] 1 THEN
              Locale.intro_locales_tac {strict = false, eager = true} ctxt [])
        val signed_word_data = {
          hget = hget,
          hupd = hupd,
          hvalid = hvalid,
          atomic_upds = #atomic_upds data,
          pointer_lense_axiom =
            get_interpretation lthy (\<^infer_instantiate>\<open>g = hget and u = hupd in
                prop \<open>pointer_lense g u\<close>\<close> lthy) }
      in
        (Typtab.update_new (sT, signed_word_data) tab, lthy)
      end)
    end

  fun disjnt_setters_tac ctxt =
    REPEAT_ALL_NEW (DETERM' (
      match_tac ctxt (@{thms distinct_prop_zip_cons distinct_prop_zip_nil list_all_zip_cons
          list_all_zip_nil allI pointer_writer_disjnt_eq pointer_writer_disjnt_ptr_corce_signed
          pointer_writer_disjnt_ptr_corce_signed'} @
        Named_Theorems.get ctxt @{named_theorems pointer_writer_disjnt_intros})) ORELSE'
      SOLVED' (SELECT_GOAL (asm_full_simp_tac (
        (ctxt |> put_simpset HOL_ss |>
          Config.put Record.sort_updates true)
          addsimps @{thms pointer_writer_disjntI option.inject prod.inject}
          addsimprocs [@{simproc field_lookup}, @{simproc Record.update}]) 1)))

  fun construct_heap_typ (T, (All_Addressable _, _)) (tab : heap_field_info Typtab.table, lthy) =
    if TermsTypes.is_array_type T then
      construct_array_heap T tab lthy
    else Utils.timeit_msg 0 lthy
      (fn _ => "Construct typ simulation for " ^ Syntax.string_of_typ lthy T ^ " (all fields addressable)")
      (fn _ =>
    let
      val info = Symtab.lookup record_info (dest_Type T |> fst) |> the
      val constr = Const (#constructor info)

      val pT = Utils.mk_ptrT T
      val p = ("p", pT)
      val f = ("f", T --> T)
      val h = ("h", lifted_globalsT)
      val x = ("x", T)

      val fields = #fields info ~~ #updates info
        |> map (fn (ft as (fN, fT), fu) =>
          let
            val data = Typtab.lookup tab fT |> the
            val fp = mk_deref "p" (T, [ft])
          in
            (fT, Const (fN, T --> fT), Const fu, fp, data)
          end)

      val heap_getters = fields
        |> map (fn (_, _, _, fp, data) => #hget data $ Free h $ fp)

      val ((getter, getter_thm), lthy) =
        Utils.define_global_const (Binding.make ("heap_" ^ name_from_type T, \<^here>)) false
          (list_comb (constr, heap_getters)) [h, p] @{attributes [derived_heap_defs]} lthy

      val heap_setters = fields
        |> map (fn (fT, fget, _, fp, data) =>
          (betapplys (#hupd data,
            [fp, absdummy fT (fget $ (Free f $ (getter $ Free h $ Free p)))]),
          lambda (Free p) (lambda (Free x) (betapplys (#hupd data,
            [fp, absdummy fT (fget $ Free x)])))))
      val ((setter, setter_thm), lthy) =
        Utils.define_global_const (Binding.make ("heap_" ^ name_from_type T ^ "_map", \<^here>)) false
          (fold (fn h => fn s => fst h $ s) heap_setters (Free h)) [p, f, h] @{attributes [derived_heap_defs]} lthy

      val fs = info |> #fields
        |> map (HOLogic.mk_list HOLogic.stringT o single o HOLogic.mk_string o Long_Name.base_name o fst)
        |> HOLogic.mk_list (HOLogic.listT HOLogic.stringT)
      val rs = fields
        |> map (fn (fT, _, ut, fp, data) =>
            lambda (Free h) (lambda (Free p) (betapply (ut, absdummy fT (#hget data $ Free h $ fp)))))
        |> HOLogic.mk_list (lifted_globalsT --> pT --> T --> T)
      val ws = heap_setters
        |> map snd
        |> HOLogic.mk_list (pT --> T --> lifted_globalsT --> lifted_globalsT)
      val v = \<^infer_instantiate>\<open>'a=\<open>T\<close> and \<T>=\<open>open_types_T\<close> and l=\<open>heap_typing\<close> in
        term \<open>\<lambda>h (p::'a::mem_type ptr). open_types.ptr_valid \<T> (l h) p\<close>\<close> lthy

      val typ_heap_simulation_of_field = fields |> map (typ_heap_simulation_of_field lthy)

      (* should fully instantiate *)
      val prove_rule = Drule.infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy)
          [open_types_T, t_hrs, t_hrs_update, heap_typing, heap_typing_update, lift,
             fs, rs, ws, v, getter, setter])
        @{thm open_types.typ_heap_simulationI_all_addressable}
      val four_goal = Goal.prove lthy [] [] (Thm.concl_of prove_rule) (fn {context = ctxt, ...} =>
        (match_tac ctxt [prove_rule] THEN_ALL_NEW_N
        select_tactic (fn _ => [
          SOLVED_DETERM_verbose "open_types" ctxt
            (SELECT_GOAL (Locale.intro_locales_tac {strict = true, eager = false} ctxt [])),
          SOLVED_DETERM_verbose "hrs" ctxt
            (SELECT_GOAL (Locale.intro_locales_tac {strict = true, eager = false} ctxt [])),
          SOLVED_DETERM_verbose "fs" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "len rs" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "len ws" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "typ_heap_simulation_of_field" ctxt
            (SELECT_GOAL ((REPEAT_ALL_NEW (match_tac ctxt @{thms list_all_zip_zip_cons list_all_zip_zip_empty}) THEN_ALL_NEW_N
                select_tactic (fn _ => typ_heap_simulation_of_field)) 1)),
          SOLVED_DETERM_verbose "disjnt setters" ctxt
            (disjnt_setters_tac ctxt),
          SOLVED_DETERM_verbose "merge all fs" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "valid" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "getter" ctxt
            (asm_full_simp_tac (ctxt addsimps [getter_thm])),
          SOLVED_DETERM_verbose "setter" ctxt
            (asm_full_simp_tac (ctxt addsimps [setter_thm]))
        ])) 1)

      val [sim_thm, pointer_disj_thm, comp_disj_thm] = HOLogic.conj_elims lthy four_goal

      val (atomic_upds, lthy) = lthy
        |> typ_heap_simulation T getter setter v
          (fn ctxt => match_tac ctxt [sim_thm] 1)
        |> heap_field_disj (map (fn (_, _, _, _, d) => d) fields) setter [] pointer_disj_thm comp_disj_thm

    in
      (Typtab.update_new (T, {
        hget = getter,
        hupd = setter,
        hvalid = v,
        atomic_upds = atomic_upds,
        pointer_lense_axiom =
          get_interpretation lthy (\<^infer_instantiate>\<open>g = getter and u = setter in
              prop \<open>pointer_lense g u\<close>\<close> lthy) }) tab, lthy)
    end)
    | construct_heap_typ (T, (Some_Addressable k, SOME (g, s))) (tab, lthy) =
    Utils.timeit_msg 0 lthy
      (fn _ => "Construct typ simulation for " ^ Syntax.string_of_typ lthy T ^ " (partially addressable)")
      (fn _ =>
    let
      val pT = Utils.mk_ptrT T
      val p = ("p", pT)
      val f = ("f", T --> T)
      val h = ("h", lifted_globalsT)
      val x = ("x", T)

      fun lookup_upd T (name : string * typ) =
        let
          val info = Symtab.lookup record_info (dest_Type T |> fst) |> the
        in
          #fields info ~~ #updates info |> find_first (fn (n, _) => name = n) |> the |> snd
        end

      val fields = k |>
        map (fn nT =>
          let
            val fp = mk_deref "p" (T, nT)
            val (upds, fT) =
              fold_map (fn nT as (_, T') => fn T => (lookup_upd T nT, T')) nT T

            val get = absfree x (fold (fn (n, fT) => fn (T, t) =>
              (fT, Const (n, T --> fT) $ t)) nT (T, Free x) |> snd)
            val f = ("f", fT --> fT)
            val upd = absfree f (fold_rev (fn nT => fn t => Const nT $ t) upds (Free f))
            val data = Typtab.lookup tab fT |> the
          in
            (fT, get, upd, fp, data)
          end)

      val heap_getters = fields |> map (fn (fT, _, ut, fp, data) =>
          betapply (ut, absdummy fT (#hget data $ Free h $ fp)))
      val ((getter, getter_thm), lthy) =
        Utils.define_global_const (Binding.make ("heap_" ^ name_from_type T, \<^here>)) false
          (fold (fn h => fn s => h $ s) heap_getters (g $ Free h $ Free p))
          [h, p] @{attributes [derived_heap_defs]} lthy

      val heap_setters = fields |> map (fn (fT, gt, _, fp, data) =>
        (betapplys ( #hupd data,
          [fp, absdummy fT (gt $ (Free f $ (getter $ Free h $ Free p)))]),
        lambda (Free p) (lambda (Free x) (betapplys ( #hupd data,
          [fp, absdummy fT (gt $ Free x)])))))
      val partial =
        let
          val inner = Free f $ (getter $ Free h $ Free p)
          val merge_addressable_fields = \<^instantiate>\<open>'a = T and inner = \<open>inner\<close> and \<T> = \<open>open_types_T\<close>
                        in term \<open>\<lambda>old::'a::mem_type. open_types.merge_addressable_fields \<T> old inner\<close>\<close>
        in
          betapplys (pointwise_upd lthy s, [Free p, merge_addressable_fields, Free h])
        end
      val ((setter, setter_thm), lthy) =
        Utils.define_global_const (Binding.make ("heap_" ^ name_from_type T ^ "_map", \<^here>)) false
          (fold (fn h => fn s => fst h $ s) heap_setters partial) [p, f, h] @{attributes [derived_heap_defs]} lthy

      val fs = k
        |> map (HOLogic.mk_list HOLogic.stringT o map (HOLogic.mk_string o Long_Name.base_name o fst))
        |> HOLogic.mk_list (HOLogic.listT HOLogic.stringT)
      val rs = heap_getters
        |> map (fn t => lambda (Free h) (lambda (Free p) t))
        |> HOLogic.mk_list (lifted_globalsT --> pT --> T --> T)
      val ws = heap_setters
        |> map snd
        |> HOLogic.mk_list (pT --> T --> lifted_globalsT --> lifted_globalsT)
      val v = \<^infer_instantiate>\<open>'a=\<open>T\<close> and \<T>=\<open>open_types_T\<close> and l=\<open>heap_typing\<close> in
        term \<open>\<lambda>h (p::'a::mem_type ptr). open_types.ptr_valid \<T> (l h) p\<close>\<close> lthy

      val typ_heap_simulation_of_field = fields |> map (typ_heap_simulation_of_field lthy)

      (* should fully instantiate *)
      val prove_rule = Drule.infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy)
          [open_types_T, t_hrs, t_hrs_update, heap_typing, heap_typing_update, lift, fs, g, s, rs, ws, v, getter, setter])
        @{thm open_types.typ_heap_simulationI_part_addressable}
      val four_goal = Goal.prove lthy [] [] (Thm.concl_of prove_rule) (fn {context = ctxt, ...} =>
        (match_tac ctxt [prove_rule] THEN_ALL_NEW_N
        select_tactic (fn _ => [
          SOLVED_DETERM_verbose "open_types" ctxt
            (SELECT_GOAL (Locale.intro_locales_tac {strict = true, eager = false} ctxt [])),
          SOLVED_DETERM_verbose "hrs" ctxt
            (SELECT_GOAL (Locale.intro_locales_tac {strict = true, eager = false} ctxt [])),
          SOLVED_DETERM_verbose "fs" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "lense" ctxt
            (asm_full_simp_tac (ctxt addsimps [@{thm lense_def}])),
          SOLVED_DETERM_verbose "len rs" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "len ws" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "typ_heap_simulation_of_field" ctxt
            (SELECT_GOAL ((REPEAT_ALL_NEW (match_tac ctxt @{thms list_all_zip_zip_cons list_all_zip_zip_empty}) THEN_ALL_NEW_N
                select_tactic (fn _ => typ_heap_simulation_of_field)) 1)),
          SOLVED_DETERM_verbose "disjnt setters" ctxt
            (disjnt_setters_tac ctxt),
          SOLVED_DETERM_verbose "disjnt setters w.r.t. setter" ctxt
            (REPEAT_ALL_NEW (DETERM' (
              match_tac ctxt (@{thms  list_all_cons list_all_nil allI} @
                Named_Theorems.get ctxt @{named_theorems disjnt_heap_fields_comp})) ORELSE'
              SOLVED' (asm_full_simp_tac (ctxt addsimps @{thms fun_eq_iff})))),
          SOLVED_DETERM_verbose "lift setter commute" ctxt
            (asm_full_simp_tac (ctxt addsimps [lift_def])),
          SOLVED_DETERM_verbose "r stack zero" ctxt
            (asm_full_simp_tac (ctxt addsimps [lift_def])),
          SOLVED_DETERM_verbose "heap_typing u commute" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "valid" ctxt
            (asm_full_simp_tac ctxt),
          SOLVED_DETERM_verbose "getter" ctxt
            (asm_full_simp_tac (put_simpset HOL_basic_ss lthy addsimps ([getter_thm] @ @{thms fold.simps comp_apply id_apply}))),
          SOLVED_DETERM_verbose "setter" ctxt
            (asm_full_simp_tac (put_simpset HOL_basic_ss lthy addsimps ([setter_thm] @ @{thms fold.simps comp_apply id_apply})))
        ])) 1)

      val [sim_thm, pointer_thm, pointer_disj_thm, comp_disj_thm] = HOLogic.conj_elims lthy four_goal

      val (atomic_upds, lthy) = lthy
        |> typ_heap_simulation T getter setter v
          (fn ctxt => match_tac ctxt [sim_thm] 1)
        |> interpret {
            locale = @{locale "pointer_lense"},
            qualifier = "dedicated_heap_" ^ name_from_type T,
            qualifier_mandatory = true,
            params = [g, pointwise_upd lthy s] }
          (fn ctxt => match_tac ctxt [pointer_thm] 1)
        |> heap_field_disj (map (fn (_, _, _, _, d) => d) fields)
          setter [pointwise_upd lthy s] pointer_disj_thm comp_disj_thm

    in
      (Typtab.update_new (T, {
        hget = getter,
        hupd = setter,
        hvalid = v,
        atomic_upds = atomic_upds,
        pointer_lense_axiom =
          get_interpretation lthy (\<^infer_instantiate>\<open>g = getter and u = setter in
              prop \<open>pointer_lense g u\<close>\<close> lthy) }) tab, lthy)
    end)
    | construct_heap_typ (T, (None_Addressable, SOME (g, s))) (tab, lthy) =
      Utils.timeit_msg 0 lthy
      (fn _ => "Construct typ simulation for " ^ Syntax.string_of_typ lthy T ^ " (nothing addressable)")
      (fn _ =>
    let
      val u = pointwise lthy s
      val v = \<^infer_instantiate>\<open>'a=\<open>T\<close> and \<T>=\<open>open_types_T\<close> and l=\<open>heap_typing\<close> in
        term \<open>\<lambda>h (p::'a::mem_type ptr). open_types.ptr_valid \<T> (l h) p\<close>\<close> lthy
      val thm = Drule.infer_instantiate' lthy
        [SOME (Thm.cterm_of lthy open_types_T), NONE, NONE, NONE, NONE, NONE,
            SOME (Thm.cterm_of lthy g), SOME (Thm.cterm_of lthy s)]
        @{thm open_types.typ_heap_simulationI_no_addressable}

      val atomic_upds = Ord_List.make Term_Ord.fast_term_ord [u]
      val lthy = lthy
        |> interpret {
            locale = @{locale lense},
            qualifier = "heap_" ^ name_from_type T ^ "_lense",
            qualifier_mandatory = true,
            params = [g, s]
          }
          (fn ctxt =>
            DETERM (Locale.intro_locales_tac {strict = false, eager = true} ctxt []) THEN
            ALLGOALS (asm_full_simp_tac ctxt))
        |> typ_heap_simulation T g u v
          (fn ctxt =>
            resolve_tac ctxt [thm] 1 THEN
            DETERM (Locale.intro_locales_tac {strict = false, eager = true} ctxt []) THEN
            ALLGOALS (asm_full_simp_tac (ctxt addsimps [lift_def])))
    in
      (Typtab.update_new (T, {
        hget = g, hupd = u, hvalid = v, atomic_upds = atomic_upds,
        pointer_lense_axiom =
          get_interpretation lthy (\<^infer_instantiate>\<open>g = g and u = u in
              prop \<open>pointer_lense g u\<close>\<close> lthy) }) tab, lthy)
      |> (fn (tab, lthy) =>
        if is_word T then construct_signed_heap T tab lthy else (tab, lthy))
    end)
    | construct_heap_typ _ _ = error "construct_heap_typ"

  fun construct_lense (g, s) =
    interpret {
      locale = @{locale lense},
      qualifier = g |> dest_Const |> fst |> Long_Name.base_name,
      qualifier_mandatory = true,
      params = [g, s]
    }
    (fn ctxt =>
      DETERM (Locale.intro_locales_tac {strict = false, eager = true} ctxt []) THEN
      ALLGOALS (asm_full_simp_tac ctxt))

  fun disj_global_virtual tab disjnt_heap_fields_comp (T, _) (g, s) lthy =
    let
      val d = Typtab.lookup tab T |> the
      val atomic_lense = get_interpretation lthy
        (\<^infer_instantiate>\<open>getter=\<open>g\<close> and setter=s in prop \<open>lense getter setter\<close>\<close> lthy)

      val disj_thm = Goal.prove lthy [] []
        (\<^infer_instantiate>\<open> upd = \<open>#hupd d\<close> and w = \<open>s\<close> in
          prop \<open>\<And>p f g. upd p f o w g = w g o upd p f\<close>\<close> lthy)
        (fn { context, ... } => REPEAT_ALL_NEW (
          DETERM' (match_from_net_tac context disjnt_heap_fields_comp) ORELSE'
          SOLVED' (asm_full_simp_tac (context addsimps @{thms fun_eq_iff}))) 1)
      val update_thms = [@{thm comp_eq_dest} OF [disj_thm]]
      val read_thms = [@{thm lense.get_commute_of_commute} OF [atomic_lense, disj_thm]]
    in
      lthy
      |> note Binding.empty @{attributes [update_commute, simp]} update_thms
      |> note Binding.empty @{attributes [update_commute, simp]} read_thms
    end

  fun overlapping_thms d1 d2 lthy =
    let
      val disj_thm = Goal.prove lthy [] []
        (\<^infer_instantiate>\<open>w1 = \<open>#hupd d2\<close> and w2 = \<open>#hupd d1\<close> in
          prop \<open>\<And>f g. pointer_writer_disjnt (\<lambda>p. w1 p f) (\<lambda>p. w2 p g)\<close>\<close> lthy)
        (fn { context, ... } => REPEAT_ALL_NEW (match_tac context
          (Named_Theorems.get context @{named_theorems pointer_writer_disjnt_intros}) ORELSE'
          SOLVED' (asm_full_simp_tac (context addsimps @{thms pointer_writer_disjntI}))) 1)
    in
      ([@{thm pointer_writer_disjntD} OF [disj_thm]],
       [@{thm pointer_lense.read_commute_of_pointer_writer_disjnt'} OF [#pointer_lense_axiom d1, disj_thm],
        @{thm pointer_lense.read_commute_of_pointer_writer_disjnt} OF [#pointer_lense_axiom d2, disj_thm]])
    end

  fun disj_atomic_virtual tab disjnt_heap_fields_comp T1 (T2, _) lthy =
    let
      val d1 = Typtab.lookup tab T1 |> the
      val d2 = Typtab.lookup tab T2 |> the

      fun independent lthy =
        let
          val atomic_setter = dest_pointwise (#hupd d1) |> the
          val atomic_lense = get_interpretation lthy
            (\<^infer_instantiate>\<open>getter=\<open>#hget d1\<close> and setter=atomic_setter
              in prop \<open>lense getter setter\<close>\<close> lthy)

          val disj_thm = Goal.prove lthy [] []
            (\<^infer_instantiate>\<open> upd = \<open>#hupd d2\<close> and w = \<open>atomic_setter\<close> in
              prop \<open>\<And>p f g. upd p f o w g = w g o upd p f\<close>\<close> lthy)
            (fn { context, ... } => REPEAT_ALL_NEW (
              DETERM' (match_from_net_tac context disjnt_heap_fields_comp) ORELSE'
              SOLVED' (asm_full_simp_tac (context addsimps @{thms fun_eq_iff}))) 1)
        in
          ([@{thm comp_eq_dest} OF [disj_thm]],
           [@{thm lense.get_commute_of_commute} OF [atomic_lense, disj_thm],
            @{thm pointer_lense.read_commute_of_commute} OF [#pointer_lense_axiom d2, disj_thm]])
        end

      val (update_thms, read_thms) =
        if Ord_List.member Term_Ord.fast_term_ord (#atomic_upds d2) (#hupd d1) then
          overlapping_thms d1 d2 lthy
        else
          independent lthy
    in
      lthy
      |> note Binding.empty @{attributes [update_commute, simp]} update_thms
      |> note Binding.empty @{attributes [update_commute, simp]} read_thms
    end

  fun disj_virtual_virtual tab disjnt_heap_fields_comp ((T1, _), (T2, _)) lthy =
    let
      val d1 = Typtab.lookup tab T1 |> the
      val d2 = Typtab.lookup tab T2 |> the
      val common = Ord_List.inter Term_Ord.fast_term_ord (#atomic_upds d1) (#atomic_upds d2)

      fun indep lthy =
        let
          val disj_thm = Goal.prove lthy [] []
            (\<^infer_instantiate>\<open> upd1 = \<open>#hupd d2\<close> and upd2 = \<open>#hupd d1\<close> in
              prop \<open>\<And>p f q g. upd2 p f o upd1 q g = upd1 q g o upd2 p f\<close>\<close> lthy)
            (fn { context, ... } => REPEAT_ALL_NEW (
              DETERM' (match_from_net_tac context disjnt_heap_fields_comp) ORELSE'
              SOLVED' (asm_full_simp_tac (context addsimps @{thms fun_eq_iff}))) 1)
        in
          ([@{thm comp_eq_dest} OF [disj_thm]],
           [@{thm pointer_lense.read_commute_of_commute'} OF [#pointer_lense_axiom d2, disj_thm],
            @{thm pointer_lense.read_commute_of_commute} OF [#pointer_lense_axiom d1, disj_thm]])
        end

      val (update_thms, read_thms) = if null common then indep lthy else overlapping_thms d1 d2 lthy
    in
      lthy
      |> note Binding.empty @{attributes [update_commute, simp]} update_thms
      |> note Binding.empty @{attributes [update_commute, simp]} read_thms
    end

  val (heap_fields_tab, lthy) = lthy
    |> pair (Typtab.make [])
    |> fold construct_heap_typ (merge_heap_fields heapTs (map Const getters ~~ map Const setters))

  val disjnt_heap_fields_comp = Named_Theorems.get lthy @{named_theorems disjnt_heap_fields_comp}
    |> (fn disj_thms => disj_thms @ map (fn thm => @{thm sym} OF [thm]) disj_thms)
    |> Tactic.build_net

  val static_fields = take (length copied_fields) all_fields
  val lthy = Utils.timeit_msg 0 lthy (fn _ => "Prove heap field commutation rules [update_commute]") (fn _ => lthy
    |> Config.put Record.sort_updates true
    |> Utils.timeap_msg 1 lthy (fn _ => "Global field lenses") (fold construct_lense static_fields)
    |> Utils.timeap_msg 1 lthy (fn _ => "Global fields vs virtual heaps") (fold (fn T => fold (disj_global_virtual heap_fields_tab disjnt_heap_fields_comp T) static_fields) orderedTs)
    |> Utils.timeap_msg 1 lthy (fn _ => "Atomic vs virtual heaps") (fold (fn T => fold (disj_atomic_virtual heap_fields_tab disjnt_heap_fields_comp T) orderedTs) atomicTs)
    |> Utils.timeap_msg 1 lthy (fn _ => "Virtual vs virtual heaps") (fold (disj_virtual_virtual heap_fields_tab disjnt_heap_fields_comp) (triangle orderedTs)))

  val thy = lthy |> Local_Theory.exit_global
in
  ((lifted_globalsT, lifted_globals_equality, heap_typing, heap_typing_update, open_types_T, ptr_valids,
      map (fn ((a, T), (b, _)) => (a, b, T)) (existing_fields ~~ new_copied_fields),
      heapTs, heap_fields_tab,
      lift, lift_def, lift_simp_thms), thy)
end

(*
 * Fetch information about structures in the program, such as
 * the fields of each structure and their types.
 *
 * We return a tuple containing (
 *     <mapping from struct names to field information>,
 *     <mapping from struct typs to field information>
 * ).
 *)
fun get_prog_struct_info ctxt prog_info =
let
  (* Fetch the namespace we are working in. *)
  val namespace =
    Long_Name.explode (dest_Type (ProgramInfo.get_globals_type prog_info) |> fst)
    |> hd |> Long_Name.explode |> hd

  (* Fetch information about structures defined in the program. *)
  val struct_data = ProgramAnalysis.get_pruned_senv (ProgramInfo.get_csenv prog_info)
        @ ProgramAnalysis.get_globals_rcd (ProgramInfo.get_csenv prog_info)

  (* Given the name of a struct ("struct foo" would be "foo_C"), return
   * the type of that structure. *)
  fun get_struct_type name =
    CalculateState.ctype_to_typ ctxt (CTypeDatatype.StructTy name)

  (* Generate information relating to a field of a single struct. *)
  fun get_field_info struct_name struct_type (field_name, (field_type, _)) = let
    val hol_field_type = CalculateState.ctype_to_typ ctxt field_type
  in
    {
      name = field_name,
      field_type = hol_field_type,
      getter =
        Const (Long_Name.implode [namespace, struct_name, field_name],
            struct_type --> hol_field_type),
      setter =
        Const (Long_Name.implode [namespace, struct_name, field_name ^ "_update"],
            (hol_field_type --> hol_field_type) --> struct_type --> struct_type)
    }
  end

  fun active_fields CType.Struct flds = flds
    | active_fields (CType.Union active) flds = filter (member (op =) active o fst) flds

  (* Generate info relating to a single struct. *)
  fun get_struct_info (struct_name, (kind, fields, _, _)) =
  let
    val struct_fields = active_fields kind fields
    val struct_type = get_struct_type struct_name
  in
    (struct_name, {
      name = struct_name,
      struct_type = struct_type,
      field_info = map (get_field_info struct_name struct_type) struct_fields
    })
  end

  val struct_info = map get_struct_info struct_data
in
  (Symtab.make struct_info,
      Typtab.make (map (fn (a,b) => (get_struct_type a, b)) struct_info))
end

fun mk_heap_info
  (ctxt : Proof.context)
  (prog_info : ProgramInfo.prog_info)
  (lifted_globalsT : typ)
  (lifted_globals_equality : thm)
  (heap_typing : term)
  (heap_typing_update : term)
  (open_types_T : term)
  (ptr_valids: (typ * (term * thm * thm)) list)
  (all_heapTs : (typ * addressable_kind) list)
  (pointwise_to_heapwide_thms: thm list)
  (lift_fn : string * thm)
  (simp_thms : thm list)
  (global_fields : (string * string * typ) list)
  (heap_tab: heap_field_info Typtab.table) =
let
  val old_globalsT = ProgramInfo.get_globals_type prog_info
  val (structs, struct_types) = get_prog_struct_info ctxt prog_info
  fun get_getter_const name globalsT destT
      = Const (name, globalsT --> destT)
  fun get_setter_const name globalsT destT
      = Const (name ^ Record.updateN, (destT --> destT) --> globalsT --> globalsT)
in
  {
    (* Type of the new globals state. *)
    globals_type = lifted_globalsT,
    old_globals_type = old_globalsT,

    heap_typing = heap_typing,
    heap_typing_update = heap_typing_update,
    open_types_T = open_types_T,
    heap_tab = Typtab.map (K (fn {hget, hupd, hvalid, ...} => {getter = hget, setter = hupd, valid = hvalid})) heap_tab,

    heap_types = map (fn (T, _) => T) all_heapTs,
    (* Heap getters / setters. *)
    heap_getters = Typtab.map (K #hget) heap_tab,
    heap_setters = Typtab.map (K #hupd) heap_tab,
    heap_valid_getters = Typtab.map (K #hvalid) heap_tab,
    ptr_valids = ptr_valids,

    (* List of mappings between the old and new global fields. *)
    global_fields = global_fields,
    global_field_getters =
        map (fn (old_name, new_name, T) =>
          (old_name, (get_getter_const old_name old_globalsT T,
            get_getter_const new_name lifted_globalsT T)))
          global_fields
        |> Symtab.make,
    global_field_setters=
        map (fn (old_name, new_name, T) =>
          (old_name, (get_setter_const old_name old_globalsT T,
            get_setter_const new_name lifted_globalsT T)))
          global_fields
        |> Symtab.make,

    (* Function to lift the old globals type into the new globals type. *)
    lift_fn_name = fst lift_fn,
    lift_fn_thm = snd lift_fn,

    (* Function to lift old globals into new globals. *)
    lift_fn_full = Const (fst lift_fn, old_globalsT --> lifted_globalsT),

    (* Dummy state variable, used as a placeholder during translation. *)
    dummy_state = Free ("_dummy_state", lifted_globalsT),

    (* Simplification theorems for the lifting function. *)
    lift_fn_simp_thms = simp_thms,

    (* Structure information. *)
    structs = structs,
    struct_types = struct_types,

    pointwise_to_heapwide_thms = pointwise_to_heapwide_thms,
    lifted_globals_equality = lifted_globals_equality
  } : heap_info
end

fun setup
      prog_info addressable_fields
      (fn_infos: FunctionInfo.function_info Symtab.table)
      make_lifted_globals_field_name gen_word_heaps lthy =
let
  val old_globalsT = ProgramInfo.get_globals_type prog_info
  (* Generate a new globals structure. *)
  val (heapTs, addressable_fields) = get_program_heap_types prog_info addressable_fields fn_infos gen_word_heaps lthy
  val _ = Utils.verbose_msg 0 lthy (fn _ => "Defining lifted_globals...")
  val ((lifted_globalsT, lifted_globals_equality, heap_typing, heap_typing_update, open_types_T,
    ptr_valids (* FIXME: do I need this *), global_fields,
    all_heapTs, heap_tab, lift, lift_def, lift_simp_thms), lthy) = lthy
    |>  AutoCorresData.in_theory_result (
          gen_new_heap prog_info addressable_fields make_lifted_globals_field_name old_globalsT heapTs)

  val Const (lift_name, _) = lift;

  (* Derived rewrites - tweaking artefacts introduced for support of adressable struct fields *)
  fun mk_pointwise_to_heapwide T =
    let
      val d = Typtab.lookup heap_tab T |> the
      val getter = #hget d
      val setter = #hupd d
    in
    case dest_pointwise setter of SOME setter =>
      let
          val eq = \<^infer_instantiate>\<open>setter = setter and getter = getter
              in prop (schematic) \<open>(\<lambda>s. setter (\<lambda>h. h (p := f (getter s p))) s) = (setter (\<lambda>h. h (p := f (h p))))\<close>\<close> lthy
      in
        SOME (autofix_prove_future lthy [] [] eq (fn {context, ...} =>
          resolve_tac context @{thms ext} 1 THEN asm_full_simp_tac context 1))
      end
    | _ => NONE
    end

  val pointwise_to_heapwide_thms = map_filter mk_pointwise_to_heapwide (fst heapTs)

  (* Generate data structure encoding all relevant information. *)
  val heap_info = mk_heap_info lthy prog_info lifted_globalsT lifted_globals_equality heap_typing heap_typing_update
        open_types_T ptr_valids all_heapTs pointwise_to_heapwide_thms (lift_name, lift_def) lift_simp_thms
        global_fields heap_tab
in
  (heap_info, lthy)
end

(*
 * EXPERIMENTAL: define wrappers and syntax for common heap operations.
 * We use the notations "s[p]->r" for {p->r} and "s[p->r := q]" for {p->r = q}.
 * For non-fields, "s[p]" and "s[p := q]".
 * The wrappers are named like "get_type_field" and "update_type_field".
 *
 * Known issues:
 *  * Every pair of getter/setter and valid/setter lemmas should be generated.
 *    If you find yourself expanding one of the wrapper definitions, then
 *    something wasn't generated correctly.
 *
 *  * On that note, lemmas relating structs and struct fields
 *    (foo vs foo.field) are not being generated.
 *    * TODO: this problem appears in Suzuki.thy
 *
 *  * The syntax looks as terrible as c-parser's. Well, at least you won't need
 *    to subscript greek letters.
 *
 *  * Isabelle doesn't like overloaded syntax. Issue VER-412
 *)

exception NO_GETTER_SETTER (* Not visible externally *)

fun mixfix (sy, ps, p) = Mixfix (Input.string sy, ps, p, Position.no_range)

(* Define getter/setter and syntax for one struct field.
   Returns the getter/setter and their definitions. *)
fun field_syntax (heap_info : heap_info)
                 (struct_info : struct_info)
                 (field_info: field_info)
                 (new_getters, new_setters, lthy) =
let
    fun unsuffix' suffix str = if String.isSuffix suffix str then unsuffix suffix str else str
    val struct_pname = unsuffix' "_C" (#name struct_info)
    val field_pname = unsuffix' "_C" (#name field_info)
    val struct_typ = #struct_type struct_info

    val state_var = ("s", #globals_type heap_info)
    val ptr_var = ("ptr", Type (@{type_name "ptr"}, [struct_typ]))
    val val_var = ("val", #field_type field_info)

    val struct_getter = case Typtab.lookup (#heap_getters heap_info) struct_typ of
                          SOME getter => getter
                        | _ => raise NO_GETTER_SETTER
    val struct_setter = case Typtab.lookup (#heap_setters heap_info) struct_typ of
                          SOME setter => (case dest_pointwise setter of
                                            SOME setter => setter
                                          | _ => raise NO_GETTER_SETTER)
                        | _ => raise NO_GETTER_SETTER

    (* We will modify lthy soon, so may not exit with NO_GETTER_SETTER after this point *)

    (* Define field accessor function *)
    val field_getter_term = \<^infer_instantiate>\<open>heap_get = struct_getter and field_get = \<open>#getter field_info\<close> and
             s = \<open>Free state_var\<close> and ptr = \<open>Free ptr_var\<close>
          in term \<open>field_get (heap_get s ptr)\<close>\<close> lthy
    val new_heap_get_name = "get_" ^ struct_pname ^ "_" ^ field_pname
    val ((new_heap_get, _,  new_heap_get_thm), lthy) =
      Utils.define_const_args new_heap_get_name I false field_getter_term
                              [state_var, ptr_var] [] @{attributes [heap_update_syntax]} lthy

    (* Define field update function *)
    val field_setter_term = \<^infer_instantiate>\<open>heap_update = struct_setter and field_update = \<open>#setter field_info\<close> and
              s = \<open>Free state_var\<close> and ptr = \<open>Free ptr_var\<close> and val = \<open>Free val_var\<close>
            in term \<open>heap_update (%old. old(ptr := field_update (%_. val) (old ptr))) s\<close> for heap_update field_update\<close> lthy

    val new_heap_update_name = "update_" ^ struct_pname ^ "_" ^ field_pname
    val ((new_heap_update, _, new_heap_update_thm), lthy) =
      Utils.define_const_args new_heap_update_name I false field_setter_term
                              [state_var, ptr_var, val_var] [] @{attributes [heap_update_syntax]} lthy

    val getter_mixfix = mixfix ("_[_]\<rightarrow>" ^ (Syntax_Ext.escape field_pname), [1000], 1000)
    val setter_mixfix = mixfix ("_[_\<rightarrow>" ^ (Syntax_Ext.escape field_pname) ^ " := _]", [1000], 1000)

    val lthy = Local_Theory.notation true Syntax.mode_default [
                 (new_heap_get, getter_mixfix),
                 (new_heap_update, setter_mixfix)] lthy

    (* Derived rewrites - tweaking artefacts introduced for support of adressable struct fields *)
    val pointwise_to_heapwide_term = \<^infer_instantiate>\<open>heap_update = struct_setter and field_update = \<open>#setter field_info\<close> and
           heap_getter = struct_getter and heap_field_getter = new_heap_update
          in term (schematic) \<open>(\<lambda>s. heap_update (%old. old(ptr := field_update (%_. val s) (heap_getter s ptr))) s) \<equiv>
                    (\<lambda>s. heap_field_getter s ptr (val s))\<close> for heap_update field_update\<close> lthy
    val pointwise_to_heapwide_thm =
      autofix_prove_future lthy [] [] pointwise_to_heapwide_term (fn {context, ...} =>
        resolve_tac context @{thms meta_ext} 1 THEN
        asm_full_simp_tac (context addsimps [new_heap_update_thm]) 1)

    (* The struct_pname returned here must match the type_pname returned in heap_syntax.
     * new_heap_update_thm relies on this to determine what kind of thm to generate. *)
    val new_getters = Symtab.update_new (new_heap_get_name,
          (struct_pname, field_pname, new_heap_get, [new_heap_get_thm])) new_getters
    val new_setters = Symtab.update_new (new_heap_update_name,
          (struct_pname, field_pname, new_heap_update, [new_heap_update_thm, pointwise_to_heapwide_thm])) new_setters


in
  (new_getters, new_setters, lthy)
end
handle NO_GETTER_SETTER => (new_getters, new_setters, lthy)


(* Prove lemmas for the new getter/setter definitions. *)
fun new_heap_update_thm (getter_type_name, getter_field_name, getter, getter_def)
                        (setter_type_name, setter_field_name, setter, setter_def)
                        lthy =
  (* TODO: also generate lemmas relating whole-struct updates to field updates *)
  if getter_type_name = setter_type_name
     andalso not ((getter_field_name = "") = (setter_field_name = "")) then NONE else

  let val lhs = \<^infer_instantiate>\<open>get = getter and set = setter in term (schematic) \<open>get (set s p v)\<close> for get set\<close> lthy
      val rhs = if getter_type_name = setter_type_name andalso
                   getter_field_name = setter_field_name
                (* functional update *)
                then \<^infer_instantiate>\<open>get = getter in term (schematic) \<open>(get s) (p := v)\<close> for get\<close> lthy
                (* separation *)
                else \<^infer_instantiate>\<open>get = getter in term (schematic) \<open>get s\<close> for get\<close> lthy
      val prop = \<^infer_instantiate>\<open>lhs = lhs and rhs = rhs in prop \<open>lhs = rhs\<close>\<close> lthy
      val defs = getter_def @ setter_def
      val thm = autofix_prove_future lthy [] [] prop
                  (fn {context,...} => (simp_tac (context addsimps
                                @{thms ext fun_upd_apply} @ defs) 1))
  in SOME thm end

fun new_heap_valid_thm _ (_, _, _, []) _ = NONE
  | new_heap_valid_thm valid_term (_, _, setter, setter_def::_) lthy =
  let val prop = \<^infer_instantiate>\<open>valid = valid_term and set = setter
                   in prop (schematic) \<open>valid (set s p v) q = valid s q\<close> for valid and set\<close> lthy
      val thm = autofix_prove_future lthy [] [] prop
                  (fn {context,...} => (simp_tac (context addsimps
                                [@{thm fun_upd_apply}, setter_def]) 1))
  in SOME thm end


(* Take a definition and eta contract the RHS:
     lhs = rhs s   ==>   (%s. lhs) = rhs
   This allows us to rewrite a heap update even if the state is eta contracted away. *)
fun eta_rhs lthy thm = let
  val Const (@{const_name "Pure.eq"}, _) $ lhs $ (rhs $ Var (("s", s_n), s_typ)) = term_of_thm thm
  val abs_term = \<^infer_instantiate>\<open>a = \<open>lambda (Var (("s", s_n), s_typ)) lhs\<close> and b = rhs in term \<open>a == b\<close>\<close> lthy
  val thm' = Goal.prove_future lthy [] [] abs_term
               (fn params => simp_tac (put_simpset HOL_basic_ss (#context params) addsimps thm :: @{thms atomize_eq ext}) 1)
in thm' end


(* Define syntax for one C type. This also creates new wrappers for heap updates. *)
fun heap_syntax (heap_info : heap_info)
                (heap_type : typ)
                (new_getters, new_setters, lthy) =
let
    val getter = case Typtab.lookup (#heap_getters heap_info) heap_type of
                   SOME getter => (case getter of
                                     Const c => c
                                   | _ => raise NO_GETTER_SETTER)
                 | NONE => raise TYPE ("heap_lift/heap_syntax: no getter", [heap_type], [])
    val setter = case Typtab.lookup (#heap_setters heap_info) heap_type of
                   SOME setter => (case dest_pointwise setter of
                                     SOME (Const c) => c
                                   | _ => raise NO_GETTER_SETTER)
                 | NONE => raise TYPE ("heap_lift/heap_syntax: no setter", [heap_type], [])

    fun replace_C (#"_" :: #"C" :: xs) = replace_C xs
      | replace_C (x :: xs) = x :: replace_C xs
      | replace_C [] = []
    val type_pname = name_from_type heap_type
                     |> String.explode |> replace_C |> String.implode

    val state_var = ("s", #globals_type heap_info)
    val heap_ptr_type = Type (@{type_name "ptr"}, [heap_type])
    val ptr_var = ("ptr", heap_ptr_type)
    val val_var = ("val", heap_type)

    val setter_def = \<^infer_instantiate>\<open>heap_update= \<open>Const setter\<close> and
            ptr=\<open>Free ptr_var\<close> and val = \<open>Free val_var\<close> and s = \<open>Free state_var\<close>
          in term \<open>heap_update (%old. old(ptr := val)) s\<close> for heap_update\<close> lthy
    val new_heap_update_name = "update_" ^ type_pname
    val ((new_heap_update, _, new_heap_update_thm), lthy) =
      Utils.define_const_args new_heap_update_name I false setter_def
                              [state_var, ptr_var, val_var] [] @{attributes [heap_update_syntax]} lthy

   
    val getter_mixfix = mixfix ("_[_]", [1000], 1000)
    val setter_mixfix = mixfix ("_[_ := _]", [1000], 1000)

    val lthy = Local_Theory.notation true Syntax.mode_default
               [(Const getter, getter_mixfix), (new_heap_update, setter_mixfix)] lthy

    val new_getters = Symtab.update_new (Long_Name.base_name (fst getter), (type_pname, "", Const getter, [])) new_getters
    val new_setters = Symtab.update_new (new_heap_update_name, (type_pname, "", new_heap_update, [new_heap_update_thm])) new_setters
in
    (new_getters, new_setters, lthy)
end
handle NO_GETTER_SETTER => (new_getters, new_setters, lthy)



(* Make all heap syntax and collect the results. *)
fun make_heap_syntax heap_info lthy =
    (Symtab.empty, Symtab.empty, lthy)
    (* struct fields *)
    |> Symtab.fold (fn (_, struct_info) =>
                       fold (field_syntax heap_info struct_info)
                            (#field_info struct_info)
                   ) (#structs heap_info)
    (* types *)
    |> fold (heap_syntax heap_info) (Typtab.keys (#heap_getters heap_info))

(*
 * Prepare for the heap lifting phase.
 * We need to:
 *   - define a lifted_globals type
 *   - prove generic heap lifting lemmas for the lifted_globals type
 *   - define heap syntax and rewrite rules (if heap_abs_syntax is set)
 *   - store these new results into the HeapInfo theory data
 * Note that because we are adding definitions that are required by all
 * conversions, we need to wait for all previous L2 conversions to finish,
 * limiting parallelism somewhat. This requires us to modify l2_results by
 * updating its intermediate lthys.
 *
 * These results are cached in the local theory, so we attempt to fetch an
 * existing definition (in the case that we are resuming a previous run).
 * In this scenario, we don't have to modify l2_results.
 *)
local
fun prepare_heap_lift'
    (filename : string)
    (prog_info : ProgramInfo.prog_info)
    (addressable_fields: (typ * addressable_fields_info) list)
    (* We define the lifted heap for all functions in the program, even if they are
     * not included in this translation. This allows heap lifting to work with
     * incremental translations. *)
    (all_simpl_infos : FunctionInfo.function_info Symtab.table)
    (* Settings *)
    (make_lifted_globals_field_name : string -> string)
    (gen_word_heaps : bool)
    (heap_abs_syntax : bool)
    (lthy : local_theory)
    : heap_lift_setup * local_theory =
let
  (* Set up heap_info and associated lemmas *)
  val (HL_setup, lthy) =
      case Symtab.lookup (HeapInfo.get (Proof_Context.theory_of lthy)) filename of
          SOME HL_setup => (HL_setup, lthy)
        | NONE => let
            val (heap_info, lthy) = setup prog_info addressable_fields all_simpl_infos
                                        make_lifted_globals_field_name gen_word_heaps lthy;
            val (lifted_heap_lemmas, lthy) = lifted_globals_lemmas prog_info heap_info lthy;
            val HL_setup = { heap_info = heap_info,
                             lifted_heap_lemmas = lifted_heap_lemmas,
                             heap_syntax_rewrs = [] };
            val lthy = Local_Theory.background_theory (
                  HeapInfo.map (fn tbl => Symtab.update (filename, HL_setup) tbl)) lthy;
            in (HL_setup, lthy) end;

  (* Do some extra lifting and create syntax (see field_syntax comment).
   * We do this separately because heap_abs_syntax could be enabled halfway
   * through an incremental translation. *)
  val (HL_setup, lthy) =
    if not heap_abs_syntax orelse not (null (#heap_syntax_rewrs HL_setup))
    then (HL_setup, lthy)
    else
      let
        val (heap_syntax_rewrs, lthy) =
            let
              val optcat = List.mapPartial I
              val heap_info = #heap_info HL_setup

              (* Define the new heap operations and their syntax. *)
              val (new_getters, new_setters, lthy) =
                make_heap_syntax heap_info lthy

              (* Make simplification thms and add them to the simpset. *)
              val update_thms = map (fn get => map (fn set => new_heap_update_thm get set lthy)
                                      (Symtab.dest new_setters |> map snd))
                                  (Symtab.dest new_getters |> map snd)
                                |> List.concat
              val valid_thms = map (fn valid => map (fn set => new_heap_valid_thm valid set lthy)
                                                    (Symtab.dest new_setters |> map snd))
                                   (Typtab.dest (#heap_valid_getters heap_info) |> map snd)
                               |> List.concat
              val thms = update_thms  @ valid_thms |> optcat

              val (_, lthy) = Utils.define_lemmas "heap_abs_simps" thms [Simplifier.simp_add] lthy
              (* Rewrite rules for converting the program. *)
              val getter_thms = Symtab.dest new_getters |> map (#4 o snd) |> flat
              val setter_thms = Symtab.dest new_setters |> map (#4 o snd) |> flat
              val (eta_setter_thms, aux_thms) = Utils.split_map_filter (try (eta_rhs lthy)) setter_thms

              val rewrite_thms = map (fn thm => @{thm symmetric} OF [thm])
                                     (getter_thms @ eta_setter_thms)
              val aux_thms = map (Raw_Simplifier.rewrite_rule lthy rewrite_thms) aux_thms
              val _ = tracing ("thms: " ^ string_of_thms lthy thms) 
              val _ = tracing ("rewrite_thms: " ^ string_of_thms lthy rewrite_thms) 
              val _ = tracing ("aux_thms: " ^ string_of_thms lthy aux_thms) 
            in (rewrite_thms @ aux_thms, lthy) end;
        val HL_setup = {heap_info = #heap_info HL_setup,
              lifted_heap_lemmas = #lifted_heap_lemmas HL_setup,
              heap_syntax_rewrs = map (Morphism.thm (Local_Theory.target_morphism lthy)) heap_syntax_rewrs};

        val lthy = Local_Theory.background_theory (
              HeapInfo.map (fn tbl => Symtab.update (filename, HL_setup) tbl)) lthy;
      in (HL_setup, lthy) end;
  in (HL_setup, lthy) end;
in
fun prepare_heap_lift
    (filename : string)
    (prog_info : ProgramInfo.prog_info)
    (addressable_fields: (typ * addressable_fields_info) list)
    (* We define the lifted heap for all functions in the program, even if they are
     * not included in this translation. This allows heap lifting to work with
     * incremental translations. *)
    (all_simpl_infos : FunctionInfo.function_info Symtab.table)
    (* Settings *)
    (make_lifted_globals_field_name : string -> string)
    (gen_word_heaps : bool)
    (heap_abs_syntax : bool)
    (lthy : local_theory)
    : heap_lift_setup * local_theory
  =
    AutoCorresData.in_theory_result'  (
      prepare_heap_lift' filename prog_info addressable_fields all_simpl_infos make_lifted_globals_field_name
      gen_word_heaps heap_abs_syntax) lthy
end

end
