(* Utilities for manipulating shallow expression syntax *)

signature EXPR_UTIL =
sig
  val const_or_free: Proof.context -> string -> term
  val subst_tab: term -> term Symtab.table
  val tab_subst: Proof.context -> term Symtab.table -> term
  val log_vars: term -> string list
end

structure Expr_Util : EXPR_UTIL =
struct
local
  open Syntax
in
  (* Extract a table of variable assignments for a substitution *)
  fun subst_tab' m (Const (@{const_name subst_upd}, _) $ s $ x $ e) = 
    (case x of
       Const (n, _) => subst_tab' (Symtab.update (n, e) m) s |
       Free (n, _) => subst_tab' (Symtab.update (n, e) m) s |
       _ => m) |
  subst_tab' m _ = m;

  val subst_tab = subst_tab' Symtab.empty;

  (* Insert a constant or free variable depending on whether x refers to a constant *)
  fun const_or_free ctx x = 
    let val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        val c = Consts.intern consts x
    in if (Name_Space.declared const_space c) then Const (c, dummyT) else Free (x, dummyT)
    end;

  (* Construct a substitution from a table *)
  fun tab_subst ctx m = 
    List.foldl (fn ((x, e), s) => const @{const_name subst_upd} $ s $ const_or_free ctx x $ e) 
               (const @{const_name subst_id}) 
               (Symtab.dest m);

  (* Extract the "logical variables" from an expression, excluding lenses *)
  fun log_vars (Const (@{const_name lens_get}, _) $ _ $ _) = Ord_List.make string_ord [] 
  | log_vars (Bound _) = []
  | log_vars (Abs (_, _, e)) = log_vars e
  | log_vars (Const (_, _)) = []
  | log_vars (Free (n, _)) = Ord_List.make string_ord [n]
  | log_vars (e $ f) = Ord_List.union string_ord (log_vars e) (log_vars f)
  | log_vars (Var (_, _)) = [];

end
end