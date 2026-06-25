(*  Title:      Utils.ML
    Author:     Diego Marmsoler
*)

signature SOLIDITY_UTIL =
sig
  val single: 'a list -> 'a
  val hd_tl: 'a list -> 'a * 'a list
  val get_morphism: string -> string -> theory -> morphism
  val readAs: Proof.context -> typ -> string -> term
  val capitalizeFirst: string -> string
  val decapitalizeFirst: string -> string
  val lookup_safe: (string * 'a) list -> string -> 'a
  val define_simple_datatype: (typ * sort) list * binding ->
      (typ list * bstring) list ->
        local_theory -> local_theory
  val pretty_terms: Proof.context -> term list -> Pretty.T
  val pretty_typs: Proof.context -> typ list -> Pretty.T
  val pretty_thms: Proof.context -> thm list -> Pretty.T
  val rmdup: ''a list -> ''a list
  val `` : ('a -> 'b) -> 'a -> 'a * 'b
  val list_conj: term list -> term
  val list_implies: term list * term -> term
  val mk_conj: term option -> term -> term
  val list_ex: (string * typ) list -> term -> term
end

structure Solidity_Util: SOLIDITY_UTIL =
struct

fun ``f = fn x => (x, f x);

fun list_conj [] = \<^Const>\<open>True\<close>
  | list_conj [A] = A
  | list_conj (A::As) = HOLogic.mk_conj (A, list_conj (As));

fun list_implies ([], B) = B
  | list_implies (As, B) = HOLogic.mk_imp (list_conj As, B)

fun mk_conj (SOME y) x =
  HOLogic.mk_conj (x,y)
| mk_conj NONE x = x

fun list_ex xs x =
  fold_rev (fn (nm,tp) => fn tr => HOLogic.mk_exists (nm,tp,tr)) xs x

val pretty_term = Syntax.pretty_term

fun pretty_terms ctxt trms =
  Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))

fun pretty_typ ctxt ty = Syntax.pretty_typ ctxt ty

fun pretty_typs ctxt tys =
  Pretty.block (Pretty.commas (map (pretty_typ ctxt) tys))

fun pretty_thm ctxt thm =
  pretty_term ctxt (Thm.prop_of thm)

fun pretty_thms ctxt thms =
  Pretty.block (Pretty.commas (map (pretty_thm ctxt) thms))

fun single xs =
  if length xs <> 1 then error "Not a singleton"
  else hd xs

fun hd_tl xs =
  if null xs then error "empty list"
  else (hd xs, tl xs)

fun readAs ctxt typ term =
  Syntax.parse_term ctxt term
  |> Type.constraint typ
  |> Syntax.check_term ctxt

fun get_morphism source target thy =
  let
    val dep = List.filter
                (fn x => #source x = source andalso #target x = target)
                (Locale.dest_dependencies [@{theory Main}] thy);
  in
    if (length dep) <> 1 then
      error "Wrong number of dependencies"
    else
      #morphism (hd dep) |> Morphism.set_context thy
  end

fun capitalizeFirst (str : string) =
    case str of
        "" => ""  (* Return an empty string if the input string is empty *)
      | s => Char.toString(Char.toUpper (String.sub (s, 0))) ^ String.substring (s, 1, size s - 1)

fun decapitalizeFirst (str : string) =
    case str of
        "" => ""  (* Return an empty string if the input string is empty *)
      | s => Char.toString(Char.toLower (String.sub (s, 0))) ^ String.substring (s, 1, size s - 1)

fun lookup_safe alist name =
  if (AList.defined (op =) alist name) then
    the (AList.lookup (op =) alist name)
  else
    error (name ^ " not defined")

fun define_simple_datatype (dt_tyargs, dt_name) constructors lthy =
  let
     val options = Plugin_Name.default_filter
     fun lift_c (tyargs, name) = (((Binding.empty, Binding.name name), map (fn t => (Binding.empty, t)) tyargs), NoSyn)
     val c_spec = map lift_c constructors
     val datatyp = ((map (fn ty => (NONE, ty)) dt_tyargs, dt_name), NoSyn)
     val dtspec =
        ((options,false),
         [(((datatyp, c_spec), (Binding.empty, Binding.empty, Binding.empty)), [])])
   in
     BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec lthy
   end;

fun rmdup aa =
  let
    fun go x y =
      if (exists (fn x' => x' = x) y) then y else x::y;
  in
    fold go aa []
  end;

end
