signature ZFUN_COMMAND =
sig
  datatype zfun = Zfun of string * (string * typ) list * typ * term * term
  datatype zfun_decl = ZfunDecl of string * (string * string) list * string * string list * string list
  val compile_zfun_decl: Proof.context -> zfun_decl -> zfun
  val compile_zfun: zfun_decl -> theory -> theory
  val parameterParser: Token.T list -> (string * string) list * Token.T list
  val nameParser: Token.T list -> (string * string) * Token.T list
  val zfun_parser: Token.T list -> zfun_decl * Token.T list
end

structure Zfun_Command: ZFUN_COMMAND =
struct

fun quint1 ((((a, b), c), d), e) = (a, b, c, d, e);

datatype zfun = Zfun of string * (string * typ) list * typ * term * term;

datatype zfun_decl = ZfunDecl of string * (string * string) list * string * string list * string list

fun add_free_types ps x = subst_free (map (fn (n, t) => (Free (n, dummyT), Free (n, t))) ps) x;

fun zfun_body (Zfun (n, ps, t, P, Q)) =
  let open Syntax; open HOLogic; open Type; open Logic;
      val res = "result"
      val Pt = constraint boolT (add_free_types ps P)
      val Qt = constraint boolT (add_free_types ((res, t) :: ps) Q)
      val p = mk_tuple (map (fn (i, t) => Free (i, t)) ps)
  in mk_equals (free n, 
                const @{const_name pfun_spec}
                  $ tupled_lambda p Pt
                  $ tupled_lambda p (tupled_lambda (Free (res, t)) Qt)) 
   end;

fun compile_zfun_decl ctx (ZfunDecl (n, ps, t, P, Q)) =
  let open Syntax; open HOLogic in
    Zfun (n, map (fn (p, t) => (p, read_typ ctx t)) ps, read_typ ctx t, Library.foldr mk_conj (map (parse_term ctx) P, @{term True}), Library.foldr mk_conj (map (parse_term ctx) Q, @{term True}))
  end;

fun compile_zfun x thy = 
  let open Syntax;
      val ctx = (Named_Target.theory_init thy)
      val f = check_term ctx (zfun_body (compile_zfun_decl ctx x))
  in Local_Theory.exit_global (snd (Specification.definition NONE [] [] ((Binding.empty, []), f) ctx))
  end;

open HOLogic;
open Parse;
open Scan;
open Syntax;

val nameParser = name -- ($$$ "::" |-- typ);

val parameterParser = 
  @{keyword "("} |-- repeat (nameParser --| @{keyword ","}) -- nameParser --| @{keyword ")"}
  >> (fn (xs, x) => xs @ [x])

val zfun_parser =
  (name -- parameterParser -- ($$$ "::" |-- typ) --
  repeat (@{keyword "precondition"} |-- term) --
  repeat (@{keyword "postcondition"} |-- term)) >> quint1 >> ZfunDecl

end
