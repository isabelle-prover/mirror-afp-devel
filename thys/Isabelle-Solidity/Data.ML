(*  Title:      Data.ML
    Author:     Diego Marmsoler
*)

signature SOLIDITY_DATA =
sig
  type store
  val Memory: store
  val Storage: store
  val Calldata: store
  type data
  type mdata
  val mlookupN: theory -> Symtab.key -> data option
  val mupdateN: Symtab.key -> data -> theory -> theory
  val a_to_b: typ -> typ
  val mk_dt_con_name: string -> string
  val c: typ
  val e: term
  val s: term
  val s': term
  val r: term
  val b: typ
  val effect: term
  val finit_map_T: typ
  val call: typ -> term
  val instantiate_b_a: typ -> typ
  val instantiate_b_a2: term -> term
  val instantiate_3: term -> term
  val instantiate_4: term -> term
  val change_types: term -> term
  val change_transfers: typ -> term -> term -> term
  val change_internals: typ -> string list -> term list -> term -> term
  val change_externals: typ -> term -> term -> term
  val mk_inv: term -> term -> term -> term
  val mk_inv_state: term -> term
  val mk_Bind: term -> term -> term
  val mk_init: term * term -> term
  val mk_write: term * term -> term
  val mk_cinit: term * term -> term
  val mk_newStack: term
  val mk_newMemory: term
  val mk_newCalldata: term
  val init_balance: term
  val init_balance_np: term
  val mk_init_storage: term -> term -> term
  val mk_exc: term -> term
  val constructor_binding: Position.T -> binding
  val mono_binding: binding -> binding
  val mk_valtype: bool option -> term -> typ
  val mk_fallback_t: typ -> typ
  val mk_local_name: Proof.context -> string -> string -> string
  val mk_True: term
  val mk_K: term -> typ list -> term * typ
  val mk_True2: term
  val mk_contract_typ: Proof.context -> string -> typ
  val post_t: term
  val rvalueT: typ
  val exT: typ
  val stateT: typ
  val smonadT: typ
  val mk_external_t: typ -> typ
  val pfun_name: string
  val con_name: string
  val mk_global_name: Proof.context -> string -> string
  val address: sort
  val rT: typ
  val mk_external: typ -> term
  val a: typ
  val solidity_command: ('a -> Toplevel.transition -> Toplevel.transition) ->
      Outer_Syntax.command_keyword ->
        string ->
          (Token.T list -> 'a * Token.T list) -> unit
  val mk_valtype_term: bool option -> term * term -> Name.context -> ((string * typ) * (term * term)) * Name.context
  val mk_inv_term': store -> ('a * term) list -> Proof.context -> ('a * ((term * (string * typ)) * term option)) list * Proof.context
  val mk_type_assms: (term * ((term * (string * typ)) * term option)) list -> term list
  val mk_type_assms_store: store -> ((string * typ) * term) list -> Proof.context -> term list * Proof.context
end

structure Solidity_Data: SOLIDITY_DATA =
struct

open Solidity_Util

datatype ptype = Par | Mem | CD

(* Data for constructor *)
type cdata =
  {term: term,                            (* Constructor constant *)
   name: string,                          (* Constructor name *)
   binding: binding,                      (* Constructor binding *)
   def: thm,                              (* Definition theorem *)
   payable: bool,                         (* Is the constructor payable *)
   parlist: ((string * typ) * term) list, (* List of value parameters *)
   memlist: ((string * typ) * term) list, (* List of memory parameters *)
   mono_name: string,                     (* Name of monotonicity property *)
   mono: thm,                             (* Monotonicity theorem *)
   dt_const: term}                        (* Constructor term for contract datatype *)

(* Data for contract methods *)
type mdata =
  {term: term,                            (* Method constant *)
   name: string,                          (* Method name *)
   binding: binding,                      (* Method binding *)
   def: thm,                              (* Definition theorem *)
   payable: bool,                         (* Is the method payable *)
   external: bool,                        (* Is the method external *)
   parlist: ((string * typ) * term) list, (* List of value parameters *)
   memlist: ((string * typ) * term) list, (* List of memory parameters *)
   cdlist: ((string * typ) * term) list,  (* List of calldata parameters *)
   mono_name: string,                     (* Name of monotonicity property *)
   mono: thm,                             (* Monotonicity theorem *)
   dt_const: term}                        (* Constructor term for contract datatype *)

(* Data for contract *)
type data =
  {dt_type: typ,                    (* Type of contract datatype *)
   dt_cases: term,                  (* Cases constant for contract datatype *)
   locale: string,                  (* Locale name for contract *)
   members: (term * term) list,     (* Name and type of the member variables *)
   constructor: cdata,              (* Constructor data *)
   methods: (string * mdata) list,  (* Method data indexed by name of the binding *)
   pfun_name: term,                 (* Contract constant *)
   pfun: thm,                       (* Definition theorem *)
   pinduct: thm}                    (* Induction theorem *)

structure MethodsN = Theory_Data
(
  type T = data Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

val mlookupN = Symtab.lookup o MethodsN.get
fun mupdateN k v = MethodsN.map (Symtab.update (k, v))

fun solidity_command trans command_keyword comment parse =
  Outer_Syntax.command command_keyword comment (parse >> trans);

fun a_to_b (TFree("'a", address)) = TFree("'b", address)
  | a_to_b T = T;

val pfun_name = "call"
fun mk_dt_con_name name = capitalizeFirst name ^ "_m"
val con_name = "constructor";
fun mk_wordT b = \<^Type>\<open>word b\<close>
fun mk_sumT (a, b) = \<^Type>\<open>sum a b\<close>;
val stringT = \<^typ>\<open>String.literal\<close>
val address = \<^sort>\<open>address\<close>
val typeT = \<^sort>\<open>type\<close>
val a = TFree("'a", address)
val b = TFree("'b", address)
val c = TFree("'c", [])

fun mk_valtype _ \<^term>\<open>SType.TValue TBool\<close> = \<^typ>\<open>bool\<close>
  | mk_valtype _ \<^term>\<open>SType.TValue TSint\<close> = \<^typ>\<open>256 word\<close>
  | mk_valtype _ \<^term>\<open>SType.TValue TAddress\<close> = b
  | mk_valtype _ (Const (\<^const_name>\<open>SType.TValue\<close>, _) $ (Const (\<^const_name>\<open>VType.TBytes\<close>, _) $ _))
    = \<^typ>\<open>string\<close>
  | mk_valtype NONE (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ _ $ _)
    = error "arrays not allowed as parameters"
  | mk_valtype NONE (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ _ $ _)
    = error "arrays not allowed as parameters"
  | mk_valtype (SOME mem) (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ _ $ _)
    = if mem then \<^Type>\<open>adata \<^Type>\<open>valtype b\<close>\<close> else  \<^Type>\<open>call_data \<^Type>\<open>valtype b\<close>\<close>
  | mk_valtype (SOME mem) (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ _)
    = if mem then \<^Type>\<open>adata \<^Type>\<open>valtype b\<close>\<close> else  \<^Type>\<open>call_data \<^Type>\<open>valtype b\<close>\<close>
  | mk_valtype _ _ = error "unsupported type"

fun instantiate_b_a t =
  let
    val vars = TVars.make1 ((("'b", 0), address), a);
  in
    Term_Subst.instantiateT vars t
  end;

fun instantiate_b_a2 t =
  let
    val vars = TVars.make1 ((("'b", 0), address), a);
  in
    Term_Subst.instantiate (vars, Vars.empty) t
  end;

fun instantiate_3 t =
  let
    val vars = TVars.make2 ((("'a", 0), typeT), \<^typ>\<open>bool\<close>) ((("'b", 0), address), TFree("'a", address));
  in
    Term_Subst.instantiate (vars, Vars.empty) t
  end;

val this = Free ("this", a)
val exT = \<^typ>\<open>ex\<close>;
val e = Free ("e", exT);
val rvalueT = \<^Type>\<open>rvalue a\<close>;
val stateT = \<^Type>\<open>state_ext a HOLogic.unitT\<close>
val s = Free ("s", stateT)
val s' = Free ("s'", stateT)
val rT = mk_sumT (HOLogic.mk_prodT (rvalueT, stateT), HOLogic.mk_prodT (exT, stateT));
val r = Free ("r", rT);
val smonadT = \<^Type>\<open>state_monad rvalueT exT stateT\<close>;

fun call name_ct = Free (pfun_name, \<^Type>\<open>fun name_ct smonadT\<close>);

fun instantiate_4 t =
  let
    val vars = TVars.make2 ((("'a", 0), typeT), smonadT) ((("'b", 0), address), TFree("'a", address));
  in
    Term_Subst.instantiate (vars, Vars.empty) t
  end;

fun change_type (_,\<^sort>\<open>address\<close>) = a
  | change_type t = TFree t;

fun change_types x = Term.map_types (fn t => Term.map_type_tfree change_type t) x;

fun change_transfer ct x (Const ("local.transfer_monad", _)) = Const ("local.transfer_monad", (ct --> smonadT) --> smonadT --> smonadT --> smonadT) $ x
  | change_transfer _ _ y = y;
fun change_transfers ct x = Term.map_aterms (change_transfer ct x);

val external = "external";
fun mk_external_t name = (name --> smonadT) --> smonadT;

fun mk_external ct = Free (external, mk_external_t ct)

fun change_external ct x (Free ("external", _)) = mk_external ct $ x
  | change_external _ _ y = y;

fun change_externals ct x = Term.map_aterms (change_external ct x);

fun obtain terms name =
  let
    val x = List.find (fn y => Term.is_Const y andalso Long_Name.base_name (fst (Term.dest_Const y)) = name) terms
  in
    if Option.isSome x then Option.valOf x else error ("aa")
  end

fun mk_internal ct terms y = call ct $ instantiate_b_a2 (obtain terms (mk_dt_con_name y))

fun change_internal ct names terms x =
  if is_Const x andalso Option.isSome (Long_Name.dest_local (fst (dest_Const x))) andalso
    exists (fn x' => x' = Option.valOf (Long_Name.dest_local (fst (dest_Const x)))) names then
    mk_internal ct terms (Option.valOf (Long_Name.dest_local (fst (dest_Const x))))
  else
    x;

fun change_internals ct names terms = Term.map_aterms (change_internal ct names terms);

fun mk_inv r P Q = \<^Const>\<open>Contract.inv a for r P Q\<close>
fun mk_inv_state i = \<^Const>\<open>Contract.inv_state a for this i\<close>

val effect = \<^Const>\<open>State_Monad.effect rvalueT exT stateT\<close>;
val kdataT = \<^Type>\<open>Stores.kdata a\<close>
val finit_map_T = \<^Type>\<open>Finite_Map.fmap stringT kdataT\<close>;

fun mk_Bind x y = \<^Const>\<open>bind rvalueT exT stateT rvalueT for x \<open>\<^Const>\<open>K smonadT rvalueT for y\<close>\<close>\<close>;

fun mk_init (x, y) = \<^Const>\<open>Solidity.init a for y x\<close>;

fun mk_write (x, y) = \<^Const>\<open>Solidity.write a for y x\<close>;

fun mk_cinit (x, y) = \<^Const>\<open>Solidity.cinit a for y x\<close>;

val mk_newStack = \<^Const>\<open>newStack a\<close>

val mk_newMemory = \<^Const>\<open>newMemory a\<close>

val mk_newCalldata = \<^Const>\<open>newCalldata a\<close>

val init_balance = \<^Const>\<open>Solidity.Solidity.init_balance a for \<open>Free ("msg_value", mk_wordT \<^typ>\<open>256\<close>)\<close> this\<close>

val init_balance_np = \<^Const>\<open>Solidity.Solidity.init_balance_np a for this\<close>

fun mk_init_storage x y = \<^Const>\<open>Solidity.Contract.initStorage a for this x y\<close>

fun mk_exc x = \<^Const>\<open>exc rvalueT exT stateT for x\<close>

fun constructor_binding p = Binding.make (con_name, p);

fun mono_binding b = Binding.prefix true "mono" b;

fun mk_fallback_t name = (name --> smonadT) --> a --> smonadT;

fun mk_global_name ctxt x =
  Context.theory_base_name (Proof_Context.theory_of ctxt) ^ "." ^ x;

fun mk_local_name ctxt x y =
  (mk_global_name ctxt x) ^ "." ^ y;

fun mk_K t [] = (t, fastype_of t)
  | mk_K t (T::Ts) =
      let
        val (t,T') = mk_K t Ts
      in
        (\<^Const>\<open>K T' T for t\<close>, T --> T')
      end

val mk_True =
  fst
    (mk_K
      \<^Const>\<open>True\<close>
      [HOLogic.mk_prodT (\<^typ>\<open>String.literal\<close> --> \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>, \<^typ>\<open>nat\<close>)])

val mk_True2 =
  fst
    (mk_K
      \<^Const>\<open>True\<close>
      [stateT])

fun mk_contract_typ ctxt name_lc =
  Type (mk_global_name ctxt name_lc, [a]);  

val post_t = \<^Const>\<open>Contract.post a\<close>

fun mk_valtype_term _ (name, \<^term>\<open>SType.TValue TBool\<close>) ctxt =
    Name.variant "bl" ctxt |>> (fn x => (x, \<^typ>\<open>bool\<close>))
    |>> ``(fn x => (name, \<^Const>\<open>Bool a for \<open>Free x\<close>\<close>))
  | mk_valtype_term _ (name, \<^term>\<open>SType.TValue TSint\<close>) ctxt = 
    Name.variant "si" ctxt |>> (fn x => (x, \<^typ>\<open>256 word\<close>))
    |>> ``(fn x => (name, \<^Const>\<open>Uint a for \<open>Free x\<close>\<close>))
  | mk_valtype_term _ (name, \<^term>\<open>SType.TValue TAddress\<close>) ctxt = 
    Name.variant "ad" ctxt |>> (fn x => (x, a))
    |>> ``(fn x => (name, \<^Const>\<open>Address a for \<open>Free x\<close>\<close>))
  | mk_valtype_term _ (name, Const (\<^const_name>\<open>SType.TValue\<close>, _) $ (Const (\<^const_name>\<open>VType.TBytes\<close>, _) $ _)) ctxt = 
    Name.variant "bt" ctxt |>> (fn x => (x, \<^typ>\<open>string\<close>))
    |>> ``(fn x => (name, \<^Const>\<open>Bytes a\<close> $ Free x))
  | mk_valtype_term NONE (_, (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ _ $ _)) _ = error "unsupported type"
  | mk_valtype_term (SOME memory) (name, (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ _ $ _)) ctxt= 
    Name.variant "ar" ctxt |>> (fn x => (x, if memory then \<^Type>\<open>adata \<^Type>\<open>valtype a\<close>\<close> else \<^Type>\<open>call_data \<^Type>\<open>valtype a\<close>\<close>))
    |>> ``(fn x => (name, Free x))
  | mk_valtype_term NONE (_, (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ _)) _ = error "unsupported type"
  | mk_valtype_term (SOME memory) (name, (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ _)) ctxt = 
    Name.variant "ar" ctxt |>> (fn x => (x, if memory then \<^Type>\<open>adata \<^Type>\<open>valtype a\<close>\<close> else \<^Type>\<open>call_data \<^Type>\<open>valtype a\<close>\<close>))
    |>> ``(fn x => (name, Free x))
  | mk_valtype_term _ _ _ = error "unsupported type"

datatype store = Memory | Storage | Calldata

fun mk_inv_term ctxt store \<^term>\<open>SType.TValue TBool\<close> =
    let
      val bl = (singleton (Name.variants (Variable.names_of ctxt)) "bl", \<^typ>\<open>bool\<close>);
      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Bool a for \<open>Free bl\<close>\<close>\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Bool a for \<open>Free bl\<close>\<close>\<close>\<close>
        | Memory => \<^Const>\<open>adata.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Bool a for \<open>Free bl\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free bl) ctxt;
    in
      (((t, bl), NONE), ctxt')
    end
  | mk_inv_term ctxt store \<^term>\<open>SType.TValue TSint\<close> =
    let
      val si = (singleton (Name.variants (Variable.names_of ctxt)) "si", \<^typ>\<open>256 word\<close>);
      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Uint a for \<open>Free si\<close>\<close>\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Uint a for \<open>Free si\<close>\<close>\<close>\<close>
        | Memory => \<^Const>\<open>adata.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Uint a for \<open>Free si\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free si) ctxt;
    in
      (((t, si), NONE), ctxt')
    end
  | mk_inv_term ctxt store \<^term>\<open>SType.TValue TAddress\<close> =
    let
      val ad = (singleton (Name.variants (Variable.names_of ctxt)) "ad", a);
      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Address a for \<open>Free ad\<close>\<close>\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Address a for \<open>Free ad\<close>\<close>\<close>\<close>
        | Memory => \<^Const>\<open>adata.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Address a for \<open>Free ad\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free ad) ctxt;
      (*Why does declare term here lead to a problem?*)
    in
      (((t, ad), NONE), ctxt')
    end
  | mk_inv_term ctxt store (Const (\<^const_name>\<open>SType.TValue\<close>, _) $ (Const (\<^const_name>\<open>VType.TBytes\<close>, _) $ _)) =
    let
      val bt = (singleton (Name.variants (Variable.names_of ctxt)) "bt", \<^typ>\<open>bytes\<close>);
      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close>\<close> $ (\<^Const>\<open>Bytes a\<close> $ Free bt)
        | Calldata => \<^Const>\<open>call_data.Value \<^Type>\<open>valtype a\<close>\<close> $ (\<^Const>\<open>Bytes a\<close> $ Free bt)
        | Memory => \<^Const>\<open>adata.Value \<^Type>\<open>valtype a\<close>\<close> $ (\<^Const>\<open>Bytes a\<close> $ Free bt);
      val ctxt' = Variable.declare_names (Free bt) ctxt;
    in
      (((t, bt), NONE), ctxt')
    end
  | mk_inv_term ctxt Storage (Const (\<^const_name>\<open>SType.TMap\<close>, _) $ _ $ dtype) = 
    let
      val mp = (singleton (Name.variants (Variable.names_of ctxt)) "mp", \<^Type>\<open>State.valtype a\<close> --> \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>);
      val ctxt' = Variable.declare_names (Free mp) ctxt;
      val y = (singleton (Name.variants (Variable.names_of ctxt')) "y", \<^Type>\<open>State.valtype a\<close>);
      val ctxt'' = Variable.declare_names (Free y) ctxt';
      val (((t, (fname, ftyp)), cnj), ctxt''') = mk_inv_term ctxt'' Storage dtype;
      val t' = \<^Const>\<open>storage_data.Map \<^Type>\<open>valtype a\<close> for \<open>Free mp\<close>\<close>
      val cnj' =
        (HOLogic.mk_all (fst y, snd y,
          HOLogic.mk_exists (fname, ftyp,
           mk_conj cnj (HOLogic.mk_eq (Free mp $ Free y ,t)))))
    in
      (((t', mp), SOME cnj'), ctxt''')
    end
  | mk_inv_term ctxt store (Const (\<^const_name>\<open>SType.TEnum\<close>, _) $ dtypes) = 
    let
      val tp =
        case store of
          Storage => \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>
        | Calldata => \<^Type>\<open>call_data \<^Type>\<open>valtype a\<close>\<close>
        | Memory => \<^Type>\<open>adata \<^Type>\<open>valtype a\<close>\<close>
      val em = (singleton (Name.variants (Variable.names_of ctxt)) "em", HOLogic.listT tp);

      val ctxt' = Variable.declare_names (Free em) ctxt;    
      val (((ts,vs),cnjs),ctxt'') = fold_map (fn x => fn ctxt => mk_inv_term ctxt store x) (HOLogic.dest_list dtypes) ctxt'
                                |>> ListPair.unzip
                                |>> apfst ListPair.unzip
      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free em\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free em\<close>\<close>
        | Memory => \<^Const>\<open>adata.Array \<^Type>\<open>valtype a\<close> for \<open>Free em\<close>\<close>

      val cnj' = HOLogic.mk_list tp ts
            |> curry HOLogic.mk_eq (Free em);

      val cnj = fold mk_conj cnjs cnj'
              |> list_ex vs;
    in
      (((t, em), SOME cnj), ctxt'')
    end
  | mk_inv_term ctxt store (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ l $ dtype) = 
    let
      val tp =
        case store of
          Storage => \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>
        | Calldata => \<^Type>\<open>call_data \<^Type>\<open>valtype a\<close>\<close>
        | Memory => \<^Type>\<open>adata \<^Type>\<open>valtype a\<close>\<close>
      val ar = (singleton (Name.variants (Variable.names_of ctxt)) "ar", HOLogic.listT tp);
      val ctxt' = Variable.declare_names (Free ar) ctxt;
      val y0' = List.tabulate (HOLogic.dest_number l |> snd, K (dtype));
      val (((ts,vs),cnjs),ctxt'') = fold_map (fn x => fn ctxt => mk_inv_term ctxt store x) y0' ctxt'
                                  |>> ListPair.unzip
                                  |>> apfst ListPair.unzip

      val t =
        case store of
          Storage => \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free ar\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free ar\<close>\<close>
        | Memory => \<^Const>\<open>adata.Array \<^Type>\<open>valtype a\<close> for \<open>Free ar\<close>\<close>

      val cnj' = HOLogic.mk_list tp ts
               |> curry HOLogic.mk_eq (Free ar);

      val cnj = fold mk_conj cnjs cnj'
              |> list_ex vs;
    in
      (((t, ar), SOME cnj), ctxt'')
    end
  | mk_inv_term ctxt store (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ dtype) = 
    let
      val tp =
        case store of
          Storage => \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>
        | Calldata => \<^Type>\<open>call_data \<^Type>\<open>valtype a\<close>\<close>
        | Memory => \<^Type>\<open>adata \<^Type>\<open>valtype a\<close>\<close>
      val da = (singleton (Name.variants (Variable.names_of ctxt)) "da", HOLogic.listT tp);
      val ctxt' = Variable.declare_names (Free da) ctxt;
      val (((t, (fname, ftyp)), cnj), ctxt'') = mk_inv_term ctxt' store dtype;
      val t' =
        case store of
          Storage => \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free da\<close>\<close>
        | Calldata => \<^Const>\<open>call_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free da\<close>\<close>
        | Memory => \<^Const>\<open>adata.Array \<^Type>\<open>valtype a\<close> for \<open>Free da\<close>\<close>

      val y = (singleton (Name.variants (Variable.names_of ctxt'')) "y", \<^typ>\<open>nat\<close>);
      val t'' =
        (HOLogic.mk_exists (fname, ftyp,
         mk_conj cnj (HOLogic.mk_eq (\<^Const>\<open>List.nth tp for \<open>Free da\<close> \<open>Free y\<close>\<close>, t))))
      val cnj' =
        HOLogic.mk_all (fst y, snd y,
          (HOLogic.mk_imp
            (\<^Const>\<open>Orderings.ord_class.less \<^typ>\<open>nat\<close> for \<open>Free y\<close> \<^Const>\<open>size \<open>HOLogic.listT tp\<close> for \<open>Free da\<close>\<close>\<close>,
            t'')));
    in
      (((t', da), SOME cnj'), ctxt'')
    end
  | mk_inv_term _ _ t = error ("unsupported type" ^ @{make_string} t)

fun mk_inv_term' store members ctxt =
  let
    fun go mname (((trm, (fname, ftyp)), cnj), ctxt) = ((mname, ((trm, (fname, ftyp)), cnj)), ctxt);
  in
    fold_map (fn(x,y) => (fn ctxt => go x (mk_inv_term ctxt store y))) members ctxt
  end;

fun mk_type_assms trms =
  let
    fun go (x, ((trm, (fname, ftyp)), cnj)) =
      (HOLogic.mk_exists (fname, ftyp,
        (mk_conj cnj
          (HOLogic.mk_eq (x, trm)))))
  in
    map go trms
  end;

fun mk_type_assms_store store trms ctxt =
  map (apfst Free) trms
  |> rpair ctxt
  |-> mk_inv_term' store
  |>> mk_type_assms

end
