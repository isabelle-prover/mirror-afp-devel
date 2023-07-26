section\<open>Automatic synthesis of formulas\<close>

theory Synthetic_Definition
  imports Utils
  keywords "synthesize" :: thy_decl % "ML"
    and "synthesize_notc" :: thy_decl % "ML"
    and "from_schematic"
begin

ML\<open>
val $` = curry ((op $) o swap)
infix $`

fun pair f g x = (f x, g x)

fun print_theorem pos (thms, lthy) =
  (Proof_Display.print_theorem pos lthy thms; lthy)

fun prove_tc_form goal thms ctxt =
  Goal.prove ctxt [] [] goal
    (fn {context = ctxt', ...} =>
      rewrite_goal_tac ctxt' thms 1
      THEN TypeCheck.typecheck_tac ctxt')

fun prove_sats goal thms thm_auto ctxt =
  Goal.prove ctxt [] [] goal
    (fn {context = ctxt', ...} =>
      let val ctxt'' = ctxt' |> Simplifier.add_simp (thm_auto |> hd) in
        rewrite_goal_tac ctxt'' thms 1
        THEN PARALLEL_ALLGOALS (asm_simp_tac ctxt'')
        THEN TypeCheck.typecheck_tac ctxt''
      end)

fun is_mem \<^Const_>\<open>mem for _ _\<close> = true
  | is_mem _ = false

fun synth_thm_sats def_name term lhs set env hyps vars vs pos thm_auto lthy =
let val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1 |>> #2
    val vs' = map (Thm.term_of o #2) vs
    val vars' = map (Thm.term_of o #2) vars
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vs'
    val sats = \<^Const>\<open>apply for \<^Const>\<open>satisfies for set r_tm\<close> env\<close>
    val rhs = \<^Const>\<open>IFOL.eq \<^Type>\<open>i\<close> for sats \<^Const>\<open>succ for \<^Const>\<open>zero\<close>\<close>\<close>
    val concl = \<^Const>\<open>iff for lhs rhs\<close>
    val g_iff = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_sats g_iff thm_refs thm_auto ctxt2
    val name = Binding.name (def_name ^ "_iff_sats")
    val thm = Utils.fix_vars thm (map (#1 o dest_Free) vars') lthy
 in
   Local_Theory.note ((name, []), [thm]) lthy |> print_theorem pos
 end

fun synth_thm_tc def_name term hyps vars pos lthy =
let val (_,tm,ctxt1) = Utils.thm_concl_tm lthy term
    val (thm_refs,ctxt2) = Variable.import true [Proof_Context.get_thm lthy term] ctxt1
                    |>> #2
    val vars' = map (Thm.term_of o #2) vars
    val tc_attrib = @{attributes [TC]}
    val r_tm = tm |> Utils.dest_lhs_def |> fold (op $`) vars'
    val concl = \<^Const>\<open>mem for r_tm \<^Const>\<open>formula\<close>\<close>
    val g = Logic.list_implies(hyps, Utils.tp concl)
    val thm = prove_tc_form g thm_refs ctxt2
    val name = Binding.name (def_name ^ "_type")
    val thm = Utils.fix_vars thm (map (#1 o dest_Free) vars') ctxt2
 in
   Local_Theory.note ((name, tc_attrib), [thm]) lthy |> print_theorem pos
 end


fun synthetic_def def_name thmref pos tc auto thy =
  let
    val (thm_ref,_) = thmref |>> Facts.ref_name
    val thm = Proof_Context.get_thm thy thm_ref;
    val thm_vars = rev (Term.add_vars (Thm.full_prop_of thm) []);
    val (((_,inst),thm_tms),_) = Variable.import true [thm] thy
    val vars = map (fn v => (v, the (Vars.lookup inst v))) thm_vars;
    val (tm,hyps) = thm_tms |> hd |> pair Thm.concl_of Thm.prems_of
    val (lhs,rhs) = tm |> Utils.dest_iff_tms o Utils.dest_trueprop
    val ((set,t),env) = rhs |> Utils.dest_sats_frm
    fun relevant ts \<^Const_>\<open>mem for t _\<close> = not (Term.is_Free t) orelse
          member (op =) ts (t |> Term.dest_Free |> #1)
      | relevant _ _ = false
    val t_vars = sort_strings (Term.add_free_names t [])
    val vs = filter (member (op =) t_vars o #1 o #1 o #1) vars
    val at = fold_rev (lambda o Thm.term_of o #2) vs t
    val hyps' = filter (relevant t_vars o Utils.dest_trueprop) hyps
  in
    Local_Theory.define ((Binding.name def_name, NoSyn),
                        ((Binding.name (def_name ^ "_def"), []), at)) thy |> #2 |>
    (if tc then synth_thm_tc def_name (def_name ^ "_def") hyps' vs pos else I) |>
    (if auto then synth_thm_sats def_name (def_name ^ "_def") lhs set env hyps vars vs pos thm_tms else I)

end
\<close>
ML\<open>

local
  val synth_constdecl =
       Parse.position (Parse.string -- ((Parse.$$$ "from_schematic" |-- Parse.thm)));

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn ((bndg,thm),p) => synthetic_def bndg thm p true true))

  val _ =
     Outer_Syntax.local_theory \<^command_keyword>\<open>synthesize_notc\<close> "ML setup for synthetic definitions"
       (synth_constdecl >> (fn ((bndg,thm),p) => synthetic_def bndg thm p false false))

in

end
\<close>
text\<open>The \<^ML>\<open>synthetic_def\<close> function extracts definitions from
schematic goals. A new definition is added to the context. \<close>

(* example of use *)
(*
schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)

synthesize "\<phi>" from_schematic mem_formula_ex
*)

end
