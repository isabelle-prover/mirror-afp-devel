(*  Title:      SpecCheck/Show/show_term.ML
    Author:     Kevin Kappelmann

Show functions for terms, types, and related data structures.
*)

signature SPECCHECK_SHOW_TERM =
sig

  val term : Proof.context -> term SpecCheck_Show_Types.show
  val typ : Proof.context -> typ SpecCheck_Show_Types.show
  val thm : Proof.context -> thm SpecCheck_Show_Types.show

  val tyenv : Proof.context -> Type.tyenv SpecCheck_Show_Types.show
  val tenv : Proof.context -> Envir.tenv SpecCheck_Show_Types.show
  val env : Proof.context -> Envir.env SpecCheck_Show_Types.show

end

structure SpecCheck_Show_Term : SPECCHECK_SHOW_TERM =
struct

structure Show = SpecCheck_Show_Base

val term = Syntax.pretty_term
val typ = Syntax.pretty_typ
fun thm ctxt = term ctxt o Thm.prop_of

local 
fun show_env_aux show_entry =
  Vartab.dest
  #> map show_entry
  #> Pretty.list "[" "]"

fun show_env_entry show (s, t) = Pretty.block [show s, Pretty.str " := ", show t]

in

fun tyenv ctxt =
  let
    val show_entry = show_env_entry (typ ctxt)
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
  in show_env_aux (show_entry o get_typs) end

fun tenv ctxt =
  let
    val show_entry = show_env_entry (term ctxt)
    fun get_trms (v, (T, t)) = (Var (v, T), t)
  in show_env_aux (show_entry o get_trms) end

end

fun env ctxt env = Show.record [
    ("maxidx", Pretty.str (string_of_int (Envir.maxidx_of env))),
    ("tyenv", tyenv ctxt (Envir.type_env env)),
    ("tenv", tenv ctxt (Envir.term_env env))
  ]

end
