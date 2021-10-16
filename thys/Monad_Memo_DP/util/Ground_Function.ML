(** Define a new ground constant from an existing function definition **)

signature GROUND_FUNCTION =
sig
  val mk_fun: bool -> thm list -> binding -> local_theory -> local_theory
end

structure Ground_Function : GROUND_FUNCTION =
struct

fun add_function bind defs =
  let
    val fixes = [(bind, NONE, NoSyn)];
    val specs = map (fn def => (((Binding.empty, []), def), [], [])) defs
  in
    Function.add_function fixes specs Function_Fun.fun_config
      (fn ctxt => Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt)
end

fun dest_hol_eq_prop t =
  let val \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.eq _ for a b\<close>\<close> = t
  in (a, b) end

fun get_fun_head t =
  let
    val (t, _) = dest_hol_eq_prop t
    val t = Term.head_of t
    val Const (fun_name, fun_ty) = t
 in (fun_name, fun_ty) end

fun mk_fun termination simps binding lthy =
  let
    val eqns = map Thm.concl_of simps
    val (eqns, _) = Variable.import_terms true eqns lthy
    val (f_name, f_ty) = get_fun_head (hd eqns)
    val s = Binding.name_of binding
    val replacement = (Const (f_name, f_ty), Free (s, f_ty))
    val eqns = map (subst_free [replacement]) eqns
    fun prove_termination lthy' = lthy'
      |> Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy')
  in
    lthy
    |> add_function binding eqns |> #2
    |> termination ? (prove_termination #> #2)
  end

end
