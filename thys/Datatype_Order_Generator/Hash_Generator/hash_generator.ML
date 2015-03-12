signature HASHCODE_GENERATOR =
sig

  type info =
   {map : term,                    (* take % x. x, if there is no map *)
    phash : term,                  (* partial hash *)
    hash : term,                   (* full hash *)
    hash_def : thm option,         (* definition of hash, important for nesting *) 
    map_comp : thm option,         (* hashositionality of map, important for nesting *)
    used_positions : bool list}

  (* registers @{term hash_of :: "some_type :: linorder hash"} 
     where some_type must just be a type without type-arguments *)
  val register_hash_of : string -> local_theory -> local_theory

  val register_foreign_hash :
    typ -> (* type-constant without type-variables *)
    term -> (* hash for type *)
    local_theory -> local_theory


  val register_foreign_partial_and_full_hash :
    string -> (* long type name *)
    term -> (* map function, should be \<lambda>x. x, if there is no map *)
    term -> (* partial hash of type (hashcode, 'b)ty => hashcode, 
      where 'a is used, 'b is unused *)
    term -> (* (full) hash of type ('a \<Rightarrow> hashcode) \<Rightarrow> ('a,'b)ty \<Rightarrow> hashcode,
      where 'a is used, 'b is unused *)
    thm option -> (* hash_def, should be full_hash = phash o map ahash ..., important for nesting *)
    thm option -> (* map hashositionality, important for nesting *)
    bool list -> (*used positions*)
    local_theory -> local_theory

  datatype hash_type = HASHCODE | BNF

  val generate_hashs_from_bnf_fp : 
    string ->                 (* name of type *)
    local_theory -> 
    ((term * thm list) list * (* partial hashs + simp-rules *)
    (term * thm) list) *      (* non-partial hash + def_rule *)
    local_theory

  val generate_hash : 
    hash_type -> 
    string -> (* name of type *)
    local_theory -> local_theory

  val get_info : Proof.context -> string -> info option

  (* ensures that the info will be available on later requests *)
  val ensure_info : hash_type -> string -> local_theory -> local_theory
    
end

structure Hashcode_Generator : HASHCODE_GENERATOR =
struct

open Generator_Aux

datatype hash_type = BNF | HASHCODE

val hash_name = @{const_name "hashcode"}

val hashT = @{typ hashcode}
fun hashfunT T = T --> hashT
val hashify = map_atyps (fn _ => hashT)
fun phashfunT T = hashify T --> hashT

val max_int = 2147483648 (* 2 ^^ 31 *)

fun int_of_string s = fold
  (fn c => fn i => (1792318057 * i + Char.ord c) mod max_int)
  (String.explode s)
  0

(* all numbers in int_of_string and create_factors are primes (31-bit) *)

fun create_factor ty_name con_name i =
  (1444315237 * int_of_string ty_name +
  1336760419 * int_of_string con_name +
  2044890737 * (i + 1) 
  ) mod max_int

fun create_hashes ty_name con_name Ts = map (fn i =>
  HOLogic.mk_number hashT (create_factor ty_name con_name i)) (0 upto length Ts)
  |> HOLogic.mk_list hashT

fun create_def_size _ = 10

type info =
 {map : term,
  phash : term,
  hash : term,
  hash_def : thm option,
  map_comp : thm option,
  used_positions : bool list};

structure Data = Generic_Data (
  type T = info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (fn (info1 : info, info2 : info) => #hash info1 = #hash info2);
);

fun add_info T info = Data.map (Symtab.update_new (T, info))

val get_info = Context.Proof #> Data.get #> Symtab.lookup

fun the_info ctxt tyco =
     (case get_info ctxt tyco of
        SOME info => info
      | NONE => error ("no hash_code information available for type " ^ quote tyco))

fun declare_info tyco m p c c_def m_hash used_pos =
  Local_Theory.declaration {syntax = false, pervasive = false} (fn phi =>
    add_info tyco
     {map = Morphism.term phi m,
      phash = Morphism.term phi p,
      hash = Morphism.term phi c,
      hash_def = Option.map (Morphism.thm phi) c_def,
      map_comp = Option.map (Morphism.thm phi) m_hash,
      used_positions = used_pos})

fun register_foreign_partial_and_full_hash tyco m p c c_def m_hash eq_thm c_thm =
  declare_info tyco m p c c_def m_hash eq_thm c_thm

fun default_hash T = absdummy T @{term "0 :: hashcode"} (*%_. 0*)

fun register_foreign_hash T hash lthy =
  let 
    val tyco = (case T of Type (tyco, []) => tyco | _ => error "expected type constant with no arguments")
  in
    register_foreign_partial_and_full_hash 
      tyco (HOLogic.id_const T) hash hash NONE NONE [] lthy
  end

fun register_hash_of tyco lthy = 
  let 
    val (T,_) = typ_and_vs_of_typname (Proof_Context.theory_of lthy) tyco @{sort type}
    val hash = Const (hash_name, hashfunT T)
  in register_foreign_hash T hash lthy end
                       

fun generate_hashs_from_bnf_fp tyco lthy =
  let
    val (tycos, Ts) = mutual_recursive_types tyco lthy
    val _ = map (fn tyco => "generating hash for type " ^ quote tyco) tycos
      |> cat_lines |> writeln
    val (tfrees, used_tfrees) = type_parameters (hd Ts) lthy
    val used_positions = map (member (op =) used_tfrees o TFree) tfrees
    val cs = map (subT "h") used_tfrees
    val hash_Ts = map hashfunT used_tfrees
    val arg_hashs = map Free (cs ~~ hash_Ts)
    val dep_tycos = fold (add_used_tycos lthy) tycos []

    val map_simps = Bnf_Access.map_simps lthy tycos
    val case_simps = Bnf_Access.case_simps lthy tycos
    val maps = Bnf_Access.map_terms lthy tycos
    val map_comp_thms = Bnf_Access.map_comps lthy tycos
    

    (* primrec definitions of partial hashs *)

    fun mk_phash (tyco, T) = ("partial_hash_code_" ^ Long_Name.base_name tyco, phashfunT T)

    fun constr_terms lthy =  
      Bnf_Access.constr_terms lthy 
      #> map (apsnd (map freeify_tvars o fst o strip_type) o dest_Const)

    fun generate_phash_eqs lthy (tyco, T) =
      let
        val constrs = constr_terms lthy tyco 

        fun hash_arg T x =
          let
            val m = Generator_Aux.create_map default_hash (K o Free o mk_phash) () (K false)
              (#used_positions oo the_info) (#map oo the_info) (K o #phash oo the_info)
              tycos ((K o K) ()) T lthy
            val p = Generator_Aux.create_partial () (K false)
              (#used_positions oo the_info) (#map oo the_info) (K o #phash oo the_info)
              tycos ((K o K) ()) T lthy
          in p $ (m $ x) |> infer_type lthy end

        fun generate_eq lthy (cN, Ts) =
          let
            val arg_Ts' = map hashify Ts
            val c = Const (cN, arg_Ts' ---> hashify T)
            val xs = Name.invent_names (Variable.names_of lthy) "x" (arg_Ts') |> map Free
            val lhs = Free (mk_phash (tyco, T)) $ list_comb (c, xs)
            val rhs = @{term hash_combine} $ HOLogic.mk_list hashT (@{map 2} hash_arg Ts xs) $ create_hashes tyco cN Ts
          in HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) |> infer_type lthy end
      in map (generate_eq lthy) constrs end

    val eqs = map (generate_phash_eqs lthy) (tycos ~~ Ts) |> List.concat
    val bindings = tycos ~~ Ts |> map mk_phash
      |> map (fn (name, T) => (Binding.name name, SOME T, NoSyn))
    val ((phashs, phash_simps), lthy) = lthy
      |> BNF_LFP_Rec_Sugar.add_primrec bindings (eqs |> map (pair Attrib.empty_binding))
    val (phi, lthy) = restore_with_morphism lthy
    val phashs = map (Morphism.term phi) phashs
    val phash_simps = Bnf_Access.postprocess_prim_rec_simp_rules phash_simps
      |> map (Morphism.fact phi)

    (* definitions of hashs via partial hashs and maps *)

    fun generate_hash_def tyco lthy =
      let
        val cs = map (subT "h") used_tfrees
        val arg_Ts = map hashfunT used_tfrees
        val args = map Free (cs ~~ arg_Ts)
        val (phash, m) = AList.lookup (op =) (tycos ~~ (phashs ~~ maps)) tyco |> the
        val ts = tfrees |> map TFree |> map (fn T =>
          AList.lookup (op =) (used_tfrees ~~ args) T |> the_default (default_hash T))
        val rhs = HOLogic.mk_comp (phash, list_comb (m, ts)) |> infer_type lthy
        val abs_def = lambdas args rhs
        val name = "hash_code_" ^ Long_Name.base_name tyco
        val ((hash, (_, prethm)), lthy) =
          Local_Theory.define ((Binding.name name, NoSyn), (Attrib.empty_binding, abs_def)) lthy
        val eq = Logic.mk_equals (list_comb (hash, args), rhs)
        val thm = Goal.prove lthy (map (fst o dest_Free) args) [] eq (K (unfold_tac lthy [prethm]))
      in
        Local_Theory.note ((Binding.name (name ^ "_def"), []), [thm]) lthy
        |>> the_single o snd
        |>> `(K hash)
      end
    val ((hashs, hash_defs), lthy) = fold_map generate_hash_def tycos lthy |>> split_list
    val (phi, lthy) = restore_with_morphism lthy
    val hashs = map (Morphism.term phi) hashs
    val hash_defs = map (Morphism.thm phi) hash_defs

    (* alternative simp-rules for hashs *)

    fun generate_hash_simps (tyco, T) lthy =
      let
        val constrs = constr_terms lthy tyco

        fun hash_arg T x =
          let
            fun create_hash (T as TFree _) =
                  AList.lookup (op =) (used_tfrees ~~ arg_hashs) T
                  |> the_default (HOLogic.id_const dummyT)
              | create_hash (Type (tyco, Ts)) =
                  (case AList.lookup (op =) (tycos ~~ hashs) tyco of
                    SOME c => list_comb (c, arg_hashs)
                  | NONE =>
                      let
                        val {hash = c, used_positions = up, ...} = the_info lthy tyco
                        val ts = (up ~~ Ts) |> map_filter (fn (b, T) =>
                          if b then SOME (create_hash T) else NONE)
                      in list_comb (c, ts) end)
              | create_hash T =
                  error ("unexpected schematic variable " ^ quote (Syntax.string_of_typ lthy T))
            val hash = create_hash T
          in hash $ x |> infer_type lthy end

        fun generate_eq_thm lthy (c_T as (cN, Ts)) =
          let
            val xs = Variable.names_of lthy
              |> fold_map (fn T => Name.variant "x" #>> Free o rpair T) Ts |> fst
            fun mk_const (c, Ts) = Const (c, Ts ---> T)
            val hash_const = AList.lookup (op =) (tycos ~~ hashs) tyco |> the
            val lhs = list_comb (hash_const, arg_hashs) $ list_comb (mk_const c_T, xs)
            val rhs = @{term hash_combine} $ HOLogic.mk_list hashT (@{map 2} hash_arg Ts xs) $ create_hashes tyco cN Ts
            val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) |> infer_type lthy

            val dep_hash_defs = map_filter (#hash_def o the_info lthy) dep_tycos
            val dep_map_comps = map_filter (#map_comp o the_info lthy) dep_tycos
            val thms = prove_multi_future lthy (map (fst o dest_Free) xs @ cs) [] [eq]
              (fn {context = ctxt, ...} =>
                Goal.conjunction_tac 1
                THEN unfold_tac ctxt
                  (@{thms id_apply o_def} @
                    List.concat case_simps @
                    List.concat phash_simps @
                    dep_map_comps @ hash_defs @ dep_hash_defs @ List.concat map_simps))
          in thms end

        val thms = map (generate_eq_thm lthy) constrs |> List.concat
        val name = "hash_code_" ^ Long_Name.base_name tyco
      in
        lthy
        |> Local_Theory.note ((Binding.name (name ^ "_simps"), @{attributes [simp, code]}), thms)
        |> apfst snd
      end

    val (_, lthy) = fold_map generate_hash_simps (tycos ~~ Ts) lthy
    val (_, lthy) = restore_with_morphism lthy

  in
    ((phashs ~~ phash_simps, hashs ~~ hash_defs), lthy)
    ||> fold (fn (((((tyco, map), phash), hash), hash_def), map_comp) =>
          declare_info tyco map phash hash (SOME hash_def) (SOME map_comp) 
            used_positions)
         (tycos ~~ maps ~~ phashs ~~ hashs ~~ hash_defs ~~ map_comp_thms)
  end

fun generate_hash gen_type tyco lthy =
  let 
    val _ = is_some (get_info lthy tyco)
      andalso error ("type " ^ quote tyco ^ " does already have a hash")
  in
    case gen_type of 
      BNF => generate_hashs_from_bnf_fp tyco lthy |> snd
    | HASHCODE => register_hash_of tyco lthy
  end
  
fun ensure_info gen_type tyco lthy =
  (case get_info lthy tyco of
    SOME _ => lthy
  | NONE => generate_hash gen_type tyco lthy)

fun generate_hash_cmd tyco param = Named_Target.theory_map (
  if param = "hashcode" then generate_hash HASHCODE tyco
  else if param = "" then generate_hash BNF tyco
  else error ("unknown parameter, expecting no parameter for BNF-datatypes, " ^
         "or \"hashcode\" for types where the class-instance hashcode should be used."))

val _ =
  Theory.setup
    (Derive_Manager.register_derive "hash_code" "generate a hash function, options are () and (hashcode)" generate_hash_cmd)

end