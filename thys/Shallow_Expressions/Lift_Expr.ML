structure ExprFun = Theory_Data
  (type T = Symset.T
   val empty = Symset.empty
   val merge = Symset.merge);

structure ExprFun_Const =
struct

fun exprfun_const n ctx =  
      let open Proof_Context; open Syntax
      in case read_const {proper = true, strict = false} ctx n of
         Const (c, _) => Local_Theory.background_theory (ExprFun.map (Symset.insert c)) ctx |
         _ => raise Match
      end;
end;

Outer_Syntax.local_theory @{command_keyword "expr_function"} 
    "declare that certain constants are functions returning expressions"
    (Scan.repeat1 (Parse.term )
     >> (fn ns => 
         (fn ctx => Library.foldl (fn (ctx, n) => ExprFun_Const.exprfun_const n ctx) (ctx, ns))));

structure ExprCtr = Theory_Data
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val merge = Symtab.merge (K true));

structure ExprCtr_Const =
struct

fun exprctr_const (n, opt) ctx =  
      let open Proof_Context; open Syntax
      in case read_const {proper = true, strict = false} ctx n of
         Const (c, _) => Local_Theory.background_theory (ExprCtr.map (Symtab.update (c, (map Value.parse_int opt)))) ctx |
         _ => raise Match
      end;
end;

Outer_Syntax.local_theory @{command_keyword "expr_constructor"} 
    "declare that certain constants are expression constructors; the parameter indicates which arguments should not be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         (fn ctx => Library.foldl (fn (ctx, n) => ExprCtr_Const.exprctr_const n ctx) (ctx, ns))));

signature LIFT_EXPR =
sig
val literal_variables: bool Config.T
val pretty_print_exprs: bool Config.T
val mark_state_variables: bool Config.T
val state_id: string
val lift_expr: Proof.context -> typ -> term -> term
val read_lift_term: Proof.context -> typ -> string -> term
val mk_lift_expr: Proof.context -> typ -> term -> term
val print_expr: Proof.context -> term -> term
end

structure Lift_Expr: LIFT_EXPR =
struct

val literal_variables = Attrib.setup_config_bool \<^binding>\<open>literal_variables\<close> (K false);
val pretty_print_exprs = Attrib.setup_config_bool \<^binding>\<open>pretty_print_exprs\<close> (K true);
val mark_state_variables = Attrib.setup_config_bool \<^binding>\<open>mark_state_variables\<close> (K true);

val state_id = "\<s>";

fun lift_expr_aux ctx stT (Const (n', t), args) =
  let 
    open Syntax
    val n = (if (Lexicon.is_marked_entity n') then Lexicon.unmark_const n' else n')
    val args' = map (lift_expr ctx stT) args
  in if (n = @{const_name lens_get} orelse n = @{const_name SEXP}) 
     then Term.list_comb (Const (n', t), args)
     else if (n = @{syntax_const "_sexp_lit"})
     then Term.list_comb (hd args, tl args')
     else if (n = @{syntax_const "_sexp_evar"})
     then Term.list_comb (hd args $ Free (state_id, stT), tl args')
     else if Symset.member (ExprFun.get (Proof_Context.theory_of ctx)) n then Term.list_comb (Const (n', t), args') $ Free (state_id, stT) 
     else if (member (op =) (Symtab.keys (ExprCtr.get (Proof_Context.theory_of ctx))) n)
     (* FIXME: Allow some parameters of an expression constructor to be ignored and not lifted *) 
     then let val (SOME aopt) = (Symtab.lookup (ExprCtr.get (Proof_Context.theory_of ctx)) n) in
          Term.list_comb 
            (Const (n', t)
            , map_index (fn (i, t) => 
                         if (member (op =) aopt i) 
                         then const @{const_name SEXP} $ (lambda (Free (state_id, stT)) (lift_expr ctx stT t)) 
                         else t) args) $ Free (state_id, stT)
          end
     else
     case (Type_Infer_Context.const_type ctx n) of
      (* If it has a lens type, we insert the get function *)
      SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) 
        => Term.list_comb (const @{const_name lens_get} $ Const (n', t) $ Free (state_id, stT), args') |
      (* If the type of the constant has an input of type "'st", we assume it's a state and lift it *)
      SOME (Type (\<^type_name>\<open>fun\<close>, [TFree (a, _), _])) 
        => if a = fst (dest_TFree Lens_Lib.astateT) 
           then Term.list_comb (Const (n', t), args) $ Free (state_id, stT)
           else Term.list_comb (Const (n, t), args') |
      _ => Term.list_comb (Const (n, t), args')
  end |
lift_expr_aux ctx stT (Free (n, t), args) = 
    let open Syntax
        val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        val t' = case (Syntax.check_term ctx (Free (n, t))) of
                   Free (_, t') => t' | _ => t
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n in
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        if (Name_Space.declared const_space c) then
          lift_expr_aux ctx stT (Const (c, t), args)
        \<comment> \<open> Otherwise, we leave it alone \<close>
        else
          let val trm = 
                \<comment> \<open> We check whether the free variable has a lens type, and if so lift it as one\<close>
                case t' of 
                 Type (\<^type_name>\<open>lens_ext\<close>, _) => const @{const_name lens_get} $ Free (n, t') $ Free (state_id, stT) |
                 \<comment> \<open> Otherwise, we leave it alone, or apply it to the state variable if it's an expression constructor \<close>
                 _ => if Config.get ctx literal_variables
                        then Free (n, t) else Free (n, t) $ Free (state_id, stT)
          in Term.list_comb (trm, map (lift_expr ctx stT) args) end
  end |
lift_expr_aux _ _ (e, args) = Term.list_comb (e, args)
and 
lift_expr ctx stT (Abs (n, t, e)) = 
  if (n = state_id) then Abs (n, t, e) else Abs (n, t, lift_expr ctx stT e) |
lift_expr ctx stT (Const ("_constrain", a) $ e $ t) = (Const ("_constrain", a) $ lift_expr ctx stT e $ t) |
lift_expr ctx stT (Const ("_constrainAbs", a) $ e $ t) = (Const ("_constrainAbs", a) $ lift_expr ctx stT e $ t) |
lift_expr ctx stT e = lift_expr_aux ctx stT (Term.strip_comb e)

fun mk_lift_expr ctx stT e = 
  lambda (Free (state_id, stT)) (lift_expr ctx stT (Term_Position.strip_positions e));

fun print_expr_aux ctx (f, args) =
  let open Proof_Context
      fun sexp_evar x = if Config.get ctx literal_variables then Syntax.const "_sexp_evar" $ x else x
  in
  case (f, args) of
    (Const (@{syntax_const "_free"}, _), (Free (n, t) :: Const (@{syntax_const "_sexp_state"}, _) :: r)) => 
     sexp_evar (Term.list_comb (Syntax.const @{syntax_const "_free"} $ Free (n, t)
                              , map (print_expr ctx) r)) |
    (Const (@{const_syntax lens_get}, _), [x, Const (@{syntax_const "_sexp_state"}, _)])
      => if Config.get ctx mark_state_variables then Syntax.const @{syntax_const "_sexp_var"} $ x else x |
    (Free (n, t), [Const (@{syntax_const "_sexp_state"}, _)]) 
      => sexp_evar (Free (n, t)) | 
    _ => if (length args > 0)
         then case (List.last args) of
           Const (@{syntax_const "_sexp_state"}, _) => 
             Term.list_comb (f, map (print_expr ctx) (take (length args - 1) args)) |
           _ => Term.list_comb (f, map (print_expr ctx) args)
         else Term.list_comb (f, map (print_expr ctx) args)
   end
and 
print_expr ctx (Abs (n, t, e)) = Abs (n, t, print_expr ctx e) |
print_expr ctx e = print_expr_aux ctx (Term.strip_comb e)

fun read_lift_term ctx stT = Syntax.check_term ctx o mk_lift_expr ctx stT o Syntax.parse_term ctx

end