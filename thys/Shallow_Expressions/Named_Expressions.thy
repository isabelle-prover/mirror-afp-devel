section \<open> Named Expression Definitions \<close>

theory Named_Expressions
  imports Expressions
  keywords "edefinition" "expression" :: "thy_decl_block" and "over"
begin

text \<open> Here, we add a command that allows definition of a named expression. It provides a more
  concise version of @{command definition} and inserts the expression brackets. \<close>

ML \<open>
structure Expr_Def =
struct

  fun mk_expr_def_eq ctx term =
    case (Type.strip_constraints term) of
      Const (@{const_name "HOL.eq"}, b) $ c $ t => 
        (fst (dest_Free (fst (Term.strip_comb c))),
        @{const Trueprop} $ (Const (@{const_name "HOL.eq"}, b) $ c $ (Syntax.const @{const_name SEXP} 
            $ (lambda (Syntax.free Lift_Expr.state_id) 
                      (Lift_Expr.lift_expr ctx dummyT (Term_Position.strip_positions t)))))) |
      _ => raise Match;

  val expr_defs = [[Token.make_string (Binding.name_of @{binding expr_defs}, Position.none)]];

  fun expr_def attr decl term ctx =
  let val named_expr_defs = @{attributes [named_expr_defs]}
      val (n, eq) = mk_expr_def_eq ctx term
      val (thm, ctx0) = Specification.definition 
                   (Option.map (fn x => fst (Proof_Context.read_var x ctx)) decl) [] [] 
                   ((fst attr, map (Attrib.check_src ctx) (named_expr_defs @ snd attr)), eq) (snd (Local_Theory.begin_nested ctx))
      val ctx1 = ExprFun_Const.exprfun_const n (Local_Theory.end_nested ctx0)
  in (thm, ctx1)
  end

  fun named_expr n typ stateT expr ctx =
    let val named_expr_defs = @{attributes [named_expr_defs]}
        val term = Const (@{const_name "HOL.eq"}, dummyT) $ Syntax.free n $ expr
        val ctx' = snd (Specification.definition 
                       (SOME (Binding.name n, SOME (stateT --> typ), Mixfix.NoSyn)) [] [] 
                       ((Binding.name (n ^ "_def"), named_expr_defs), snd (mk_expr_def_eq ctx term)) (snd (Local_Theory.begin_nested ctx)))
        (* When adding an expression in a locale, the named recorded below may be the 
           localised version, which may not work correctly. This may lead to unexpected
           behaviour when there are two locales each with a constant of the same name. *)
        val ctx2 = ExprFun_Const.exprfun_const n (Local_Theory.end_nested ctx')
        in ctx2
  end


  fun named_expr_cmd n t st expr ctx =
    let val term = Syntax.parse_term ctx expr
        val stateT = Syntax.read_typ ctx st
        val typ = Syntax.read_typ ctx t
        in named_expr n typ stateT term ctx
  end

end;

val _ =
let
  open Expr_Def;
in
  Outer_Syntax.local_theory \<^command_keyword>\<open>edefinition\<close> "UTP constant definition"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, (attr, term)), _), _) =>
        (fn ctx => snd (expr_def attr decl (Syntax.parse_term ctx term) ctx))))
end

val _ =
let
  open Expr_Def;
in
  Outer_Syntax.local_theory \<^command_keyword>\<open>expression\<close> "define named expressions"
    ((((Parse.name -- Scan.optional (@{keyword "::"} |-- Parse.typ) "_" -- Scan.optional (@{keyword "over"} |-- Parse.typ) "_") --| @{keyword "is"}) -- Parse.term)  >> (fn (((n, t), st), expr) => 
        (named_expr_cmd n t st expr)))
end;

\<close>

end