fun add_archconstdefs thy =
  let
    val termof =
      HOLogic.mk_list
        (HOLogic.mk_list
          (HOLogic.mk_list (fn t => HOLogic.number_of_const HOLogic.natT $ HOLogic.mk_binum t)
             HOLogic.natT)
          (HOLogic.listT(HOLogic.natT)))
        (HOLogic.listT(HOLogic.listT(HOLogic.natT)));
    val nlll = HOLogic.listT(HOLogic.listT(HOLogic.listT(HOLogic.natT)))
    fun def c l =
      let val lhs = Const (Sign.full_name thy c,nlll)
          val rhs = termof l
      in ((Thm.def_name c, Logic.mk_equals (lhs, rhs)), []) end;
    val tri = "Tri"
    val quad = "Quad"
    val pent = "Pent"
    val hex = "Hex"
    val hept = "Hept"
    val oct = "Oct"
   in
    thy
    |> Theory.add_consts_i
        [(tri, nlll, Syntax.NoSyn), (quad, nlll, Syntax.NoSyn),
         (pent, nlll, Syntax.NoSyn), (hex, nlll, Syntax.NoSyn),
         (hept, nlll, Syntax.NoSyn), (oct, nlll, Syntax.NoSyn)]
    |> #2 o PureThy.add_defs_i false
        [def tri Tri, def quad Quad, def pent Pent, def hex Hex, def hept Hept, def oct Oct]
  end;
