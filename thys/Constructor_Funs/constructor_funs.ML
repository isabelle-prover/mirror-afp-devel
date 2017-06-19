signature CONSTRUCTOR_FUNS = sig
  val mk_funs: Ctr_Sugar.ctr_sugar -> local_theory -> local_theory
  val mk_funs_typ: typ -> local_theory -> local_theory
  val mk_funs_cmd: string -> local_theory -> local_theory

  val constructor_funs_plugin: string
  val setup: theory -> theory
end

structure Constructor_Funs : CONSTRUCTOR_FUNS = struct

structure Data = Generic_Data
(
  type T = term list * thm list * Symtab.set
  val empty = ([], [], Symtab.empty)
  fun merge ((ts1, thms1, s1), (ts2, thms2, s2)) =
    (ts1 @ ts2, thms1 @ thms2, Symtab.merge op = (s1, s2))
  val extend = I
)

fun lenient_unvarify t =
  (* type variables in records are not schematic *)
  Logic.unvarify_global t
    handle TERM _ => t

fun mk_funs {T, ctrs, ...} lthy =
  let
    val typ_name = fst (dest_Type T)

    fun mk_fun ctr lthy =
      let
        val (name, typ) = dest_Const (lenient_unvarify ctr)
        val (typs, _) = strip_type typ
        val len = length typs
      in
        if len > 0 then
          let
            val base_name = Long_Name.base_name name
            val binding = Binding.name base_name
            val args = Name.invent_names (Name.make_context [base_name]) Name.uu typs |> map Free
            val lhs = list_comb (Free (base_name, typ), args)
            val rhs = list_comb (Const (name, typ), args)
            val def = Logic.mk_equals (lhs, rhs)
            val ((term, (_, def_thm)), lthy') =
              Specification.definition NONE [] [] ((binding, []), def) lthy
            val unfold_thm = @{thm Pure.symmetric} OF [Local_Defs.abs_def_rule lthy' def_thm]
          in
            (SOME (term, unfold_thm), lthy')
          end
        else
          (NONE, lthy)
      end

    fun upd (ts', thms') =
      Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi =>
          Data.map (fn (ts, thms, s) =>
            (map (Morphism.term phi) ts' @ ts,
             map (Morphism.thm phi) thms' @ thms,
             Symtab.update_new (typ_name, ()) s)))

    val exists = Symtab.defined (#3 (Data.get (Context.Proof lthy))) typ_name
    val warn = Pretty.separate "" [Syntax.pretty_typ lthy T, Pretty.str "already processed"]
      |> Pretty.block
    val _ = if exists then warning (Pretty.string_of warn) else ()
  in
    if exists then
      lthy
    else
      Local_Theory.open_target lthy |> snd
      |> Proof_Context.concealed
      |> Local_Theory.map_background_naming
          (Name_Space.mandatory_path typ_name #> Name_Space.mandatory_path "constructor_fun")
      |> fold_map mk_fun ctrs
      |>> map_filter I |>> split_list
      |-> upd
      |> Local_Theory.close_target
    end

fun mk_funs_typ typ lthy =
  mk_funs (the (Ctr_Sugar.ctr_sugar_of lthy (fst (dest_Type typ)))) lthy

fun mk_funs_cmd s lthy =
  mk_funs_typ (Proof_Context.read_type_name {proper = true, strict = false} lthy s) lthy

val code_functrans = Code_Preproc.simple_functrans (fn ctxt => fn thms =>
  let
    val (consts, unfolds, _) = Data.get (Context.Proof ctxt)

    val conv =
      Conv.top_conv (K (Conv.try_conv (Conv.rewrs_conv unfolds))) ctxt
      |> Conv.arg_conv

    fun apply_conv thm =
      let
        val thm' = Conv.fconv_rule conv thm
        val prop = Thm.prop_of thm

        val head = Logic.dest_equals prop |> fst |> strip_comb |> fst
        val protected =
          exists (fn const => Pattern.matches (Proof_Context.theory_of ctxt) (const, head)) consts
      in
        if protected orelse Thm.prop_of thm aconv Thm.prop_of thm' then
          (false, thm)
        else
          (true, thm')
      end

    val (changeds, thms') = split_list (map apply_conv thms)
  in
    if exists I changeds then
      SOME thms'
    else
      NONE
  end)

val constructor_funs_plugin =
  Plugin_Name.declare_setup @{binding constructor_funs}

(** setup **)

val _ =
  Outer_Syntax.local_theory
    @{command_keyword "constructor_funs"}
    "defines constructor functions for a datatype and sets up the code generator"
    (Scan.repeat1 Args.embedded_inner_syntax >> fold mk_funs_cmd)

val setup =
  Code_Preproc.add_functrans ("constructor_funs", code_functrans)
  #> Ctr_Sugar.ctr_sugar_interpretation constructor_funs_plugin (mk_funs_typ o #T)

end