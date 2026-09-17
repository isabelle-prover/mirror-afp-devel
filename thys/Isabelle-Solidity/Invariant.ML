(*  
    Title:      Invariant.ML
    Author:     Diego Marmsoler
*)

signature INVARIANT =
sig
end                                                   

structure Invariant: INVARIANT =
struct

open Solidity_Util;
open Solidity_Data;

val _ = let
  val specparser =
    let
      fun mk_invariant (((name, var), inv), contract_name) thy =
        let
          val name_lc = decapitalizeFirst contract_name;
          val lthy = Named_Target.init [] (Context.theory_base_name thy ^ "." ^ name_lc) thy
          val var =
            let
              val tp = HOLogic.mk_prodT (\<^typ>\<open>String.literal\<close> --> \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>, \<^typ>\<open>nat\<close>)
            in
              readAs lthy tp var
            end;
          val (trms', ctxt) =
            let
              val data = the (mlookupN (Proof_Context.theory_of lthy) name_lc);
              val members = map (fn (t1,t2) => (HOLogic.mk_fst var $ t1, t2)) (#members data);
            in
              lthy |> Variable.declare_constraints var
                   |> mk_inv_term' Storage members
            end;
          val trms = mk_type_assms trms'

          val inv = Syntax.read_term ctxt inv |> change_types;

          val (vars, prems) =
            let
              fun go (x, ((trm, (fname, ftype)), cnj)) =
                ((fname, ftype), HOLogic.mk_Trueprop (mk_conj cnj (HOLogic.mk_eq (x, trm))))
            in
              map go trms' |> ListPair.unzip
            end;

          val varsI = fst (Term.dest_Free var) :: map fst vars
          val premsI = HOLogic.mk_Trueprop inv :: prems
          fun mytac {context, prems} def =
            rewrite_goal_tac context [def] THEN' blast_tac (context addSIs prems)

          val (tm, thm, lthy) =
            let
              val idef = lambda var (fold (curry HOLogic.mk_conj) trms inv)
              fun export ((term, (_, thm)), (lthy_new, lthy_old)) =
                let
                  val pi = Proof_Context.export_morphism lthy_old lthy_new;
                  val thms_new = (Morphism.thm pi) thm;
                  val term_new = (Morphism.term pi) term;
                in
                  (term_new, thms_new, lthy_new)
                end;
            in
              tap (K (writeln "Generating invariant definition ..."))
              Local_Theory.begin_nested lthy
              |> snd
              |> Local_Theory.define ((name, NoSyn), (Binding.empty_atts, idef)) ||> `Local_Theory.end_nested
              |> export
            end;

          val varsE = fst (Term.dest_Free var) :: ["thesis"]
          val elim =
            let
              fun go x y = Logic.all (Free x) y;
              val thesis = Free ("thesis", \<^typ>\<open>bool\<close>)
              val prems = fold go vars (Logic.list_implies (premsI, HOLogic.mk_Trueprop thesis));
            in
              Logic.mk_implies (HOLogic.mk_Trueprop (tm $ var), Logic.mk_implies (prems, HOLogic.mk_Trueprop thesis))
            end;

        in
          tap (K (writeln "Generating introduction rule ..."))
          Goal.prove lthy varsI premsI (HOLogic.mk_Trueprop (tm $ var)) (fn x => mytac x thm 1)
           |> (fn thm => Local_Theory.note ((Binding.map_name (fn x => x ^ "I") name, @{attributes [wprules]}), [thm]) lthy)
           |> snd
           |> tap (K (writeln "Generating elimination rule ..."))
           |> (fn lthy => Goal.prove lthy varsE [] elim (fn x => mytac x thm 1)
            |> (fn thm => Local_Theory.note ((Binding.map_name (fn x => x ^ "E") name, @{attributes [wperules]}), [Object_Logic.rulify lthy thm]) lthy))
           |> snd
           |> Local_Theory.exit_global
        end;
    in
      (Parse.binding -- Parse.term -- (Parse.$$$ "where" |-- Parse.term) -- (Parse.$$$ "for" |-- Parse.string)) >> mk_invariant
    end
in
  solidity_command Toplevel.theory @{command_keyword "invariant"} "creates a contract" specparser
end

end