(*  ID:         $Id: Arch.thy,v 1.8 2008-12-04 14:49:15 fhaftmann Exp $
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

setup {*
  let
    fun mk_list T f = HOLogic.mk_list T o map f;
    fun add_def (c, l) =
      let
        val term_of = mk_list @{typ "nat list list"}
          (mk_list @{typ "nat list"}
            (mk_list @{typ "nat"} (HOLogic.mk_number @{typ "nat"})));
        val eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
          (Free (c, @{typ "nat list list list"}), term_of l);
      in
        tap (fn _ => writeln ("Defining archive " ^ c))
        #> Specification.definition (SOME (Binding.name c, SOME @{typ "nat list list list"}, NoSyn),
          (Attrib.empty_binding, eq))
        #> snd
      end;
  in
    Theory_Target.init NONE
    #> add_def ("Tri", Tri)
    #> add_def ("Quad", Quad)
    #> add_def ("Pent", Pent)
    #> add_def ("Hex", Hex)
    #> add_def ("Hept", Hept)
    #> add_def ("Oct", Oct)
    #> LocalTheory.exit_global
  end
*}

text {* First the ML values are loaded.  Then they are turned into
Isabelle definitions of the constants @{const Tri}, @{const Quad},
@{const Pent}, @{const Hex}, @{const Hept}, @{const Oct}, all of type
@{typ "nat list list list"}. *}

end
