(*  ID:         $Id: Arch.thy,v 1.3 2008-04-15 17:21:57 makarius Exp $
    Author:     Tobias Nipkow
*)

header {* Archive *}

theory Arch
imports Main
uses
  "Archives/Tri.ML"
  "Archives/Quad.ML"
  "Archives/Pent.ML"
  "Archives/Hex.ML"
  "Archives/Hept.ML"
  "Archives/Oct.ML"
begin

setup {* fn thy =>
  let
    val data = [("Tri", Tri), ("Quad", Quad), ("Pent", Pent),
      ("Hex", Hex), ("Hept", Hept), ("Oct", Oct)];
    fun mk_list T f = HOLogic.mk_list T o map f;
    fun mk_def T (c, l) =
      let
        val T' = HOLogic.listT (HOLogic.listT (HOLogic.listT T))
        val term_of = mk_list (HOLogic.listT (HOLogic.listT T))
         (mk_list (HOLogic.listT T)
           (mk_list T (HOLogic.mk_number T)));
        val lhs = Const (Sign.full_name thy c, T');
        val rhs = term_of l;
      in ((c, T'), (Thm.def_name c, Logic.mk_equals (lhs, rhs))) end;
    fun add_defs defs =
      Sign.add_consts_i (map (fn ((c, T), _) => (c, T, Syntax.NoSyn)) defs)
      #> PureThy.add_defs_i false (map (fn (_, (name, prop)) => ((name, prop), [])) defs)
  in
    thy
    |> add_defs (map (mk_def HOLogic.natT) data)
    |> snd
  end;
*}

text {* First the ML values are loaded.  Then they are turned into
Isabelle definitions of the constants @{const Tri}, @{const Quad},
@{const Pent}, @{const Hex}, @{const Hept}, @{const Oct}, all of type
@{typ "nat list list list"}. *}

end
