(*  Title:      Transport/transport_util.ML
    Author:     Kevin Kappelmann

Utilities used by Transport.
*)
signature TRANSPORT_UTIL =
sig
  val transport_id : string

  (* lists *)
  val list_aggregate : ('a * 'b -> 'b) -> ('c -> 'a) -> 'b -> 'c list -> 'b
  val list_max : ('a -> int) -> int -> 'a list -> int

  (* object logic *)
  val mk_judgement : term -> term
  val dest_judgement : term -> term
  val real_thm_concl : thm -> term
  val cdest_judgement : cterm -> cterm
  val real_thm_cconcl : thm -> cterm
  val boolT : typ

  val mk_hom_rel_type : typ -> typ

  (* conversions *)
  val judgement_conv : conv -> conv

  (* bindings *)
  val concat_bindings : binding list -> binding
  val add_suffix : binding -> binding -> binding

  (* contexts *)
  val set_proof_mode_schematic : Proof.context -> Proof.context
  val set_proof_mode_pattern : Proof.context -> Proof.context

  (* definitions *)
  val create_local_theory_def : binding * mixfix -> Token.src list -> term ->
    local_theory -> (term * (string * thm)) * local_theory
  val equality_eta_expand : Proof.context -> string -> thm -> thm

  (* methods *)
  val split_conjunctions : Method.text

  (* attributes *)
  val attrib_to_src : Position.T -> attribute -> Token.src

end

structure Transport_Util : TRANSPORT_UTIL =
struct

val transport_id = "trp"

fun list_aggregate aggregate transform = List.foldl (aggregate o apfst transform)
fun list_max f = list_aggregate Int.max f

val mk_judgement = HOLogic.mk_Trueprop
val dest_judgement = HOLogic.dest_Trueprop
val real_thm_concl = dest_judgement o Thm.concl_of
val cdest_judgement = Thm.dest_comb #> snd
val real_thm_cconcl = cdest_judgement o Thm.cconcl_of
val boolT = HOLogic.boolT

fun mk_hom_rel_type T = [T, T] ---> boolT

val judgement_conv = HOLogic.Trueprop_conv

val split_conjunctions =
  Method.Basic (fn _ => SIMPLE_METHOD (HEADGOAL Goal.conjunction_tac))

fun equality_eta_expand ctxt var_name eq =
  let
    val argTs = Thm.lhs_of eq |> Thm.typ_of_cterm |> binder_types
    val fresh_args = Term_Util.fresh_vars var_name argTs (Thm.maxidx_of eq)
      |> map (Thm.cterm_of ctxt) o fst
  in fold (General_Util.flip Drule.fun_cong_rule) fresh_args eq end

val concat_bindings = Binding.conglomerate
fun add_suffix binding suffix = concat_bindings [binding, suffix]

val set_proof_mode_schematic = Proof_Context.set_mode Proof_Context.mode_schematic
val set_proof_mode_pattern = Proof_Context.set_mode Proof_Context.mode_pattern

fun create_local_theory_def (binding, mixfix) attribs t =
  Local_Theory.define ((binding, mixfix), ((Thm.def_binding binding, attribs), t))

fun attrib_to_src pos = Attrib.internal pos o K

end