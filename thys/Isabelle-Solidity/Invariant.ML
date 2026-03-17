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

fun mk_conj (SOME y) x =
  HOLogic.mk_conj (x,y)
| mk_conj NONE x = x

fun list_ex xs x =
  fold_rev (fn (nm,tp) => fn tr => HOLogic.mk_exists (nm,tp,tr)) xs x

fun mk_inv_term ctxt \<^term>\<open>SType.TValue TBool\<close> =
    let
      val bl = (singleton (Name.variants (Variable.names_of ctxt)) "bl", \<^typ>\<open>bool\<close>);
      val t = \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Bool a for \<open>Free bl\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free bl) ctxt;
    in
      (((t, bl), NONE), ctxt')
    end
  | mk_inv_term ctxt \<^term>\<open>SType.TValue TSint\<close> =
    let
      val si = (singleton (Name.variants (Variable.names_of ctxt)) "si", \<^typ>\<open>256 word\<close>);
      val t = \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Uint a for \<open>Free si\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free si) ctxt;
    in
      (((t, si), NONE), ctxt')
    end
  | mk_inv_term ctxt \<^term>\<open>SType.TValue TAddress\<close> =
    let
      val ad = (singleton (Name.variants (Variable.names_of ctxt)) "ad", a);
      val t = \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close> for \<open>\<^Const>\<open>Address a for \<open>Free ad\<close>\<close>\<close>\<close>;
      val ctxt' = Variable.declare_names (Free ad) ctxt;
    in
      (((t, ad), NONE), ctxt')
    end
  | mk_inv_term ctxt (Const (\<^const_name>\<open>SType.TValue\<close>, _) $ (Const (\<^const_name>\<open>VType.TBytes\<close>, _) $ _)) =
    let
      val bt = (singleton (Name.variants (Variable.names_of ctxt)) "bt", \<^typ>\<open>bytes\<close>);
      val t = \<^Const>\<open>storage_data.Value \<^Type>\<open>valtype a\<close>\<close> $ (\<^Const>\<open>Bytes a\<close> $ Free bt);
      val ctxt' = Variable.declare_names (Free bt) ctxt;
    in
      (((t, bt), NONE), ctxt')
    end
  | mk_inv_term ctxt (Const (\<^const_name>\<open>SType.TMap\<close>, _) $ _ $ dtype) = 
    let
      val mp = (singleton (Name.variants (Variable.names_of ctxt)) "mp", \<^Type>\<open>State.valtype a\<close> --> \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>);
      val ctxt' = Variable.declare_names (Free mp) ctxt;
      val y = (singleton (Name.variants (Variable.names_of ctxt')) "y", \<^Type>\<open>State.valtype a\<close>);
      val ctxt'' = Variable.declare_names (Free y) ctxt';
      val (((t, (fname, ftyp)), cnj), ctxt''') = mk_inv_term ctxt'' dtype;
      val t' = \<^Const>\<open>storage_data.Map \<^Type>\<open>valtype a\<close> for \<open>Free mp\<close>\<close>
      val cnj' =
        (HOLogic.mk_all (fst y, snd y,
          HOLogic.mk_exists (fname, ftyp,
           mk_conj cnj (HOLogic.mk_eq (Free mp $ Free y ,t)))))
    in
      (((t', mp), SOME cnj'), ctxt''')
    end
  | mk_inv_term ctxt (Const (\<^const_name>\<open>SType.TEnum\<close>, _) $ dtypes) = 
    let
      val em = (singleton (Name.variants (Variable.names_of ctxt)) "em", HOLogic.listT \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>);
      val ctxt' = Variable.declare_names (Free em) ctxt;    
      val (((ts,vs),cnjs),ctxt'') = fold_map (fn x => fn ctxt => mk_inv_term ctxt x) (HOLogic.dest_list dtypes) ctxt'
                                |>> ListPair.unzip
                                |>> apfst ListPair.unzip
      val t = \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free em\<close>\<close>

      val cnj' = HOLogic.mk_list \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close> ts
            |> curry HOLogic.mk_eq (Free em);

      val cnj = fold mk_conj cnjs cnj'
              |> list_ex vs;
    in
      (((t, em), SOME cnj), ctxt'')
    end
  | mk_inv_term ctxt (Const (\<^const_name>\<open>SType.TArray\<close>, _) $ l $ dtype) = 
    let
      val ar = (singleton (Name.variants (Variable.names_of ctxt)) "ar", HOLogic.listT \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>);
      val ctxt' = Variable.declare_names (Free ar) ctxt;
      val y0' = List.tabulate (HOLogic.dest_number l |> snd, K (dtype));
      val (((ts,vs),cnjs),ctxt'') = fold_map (fn x => fn ctxt => mk_inv_term ctxt x) y0' ctxt'
                                  |>> ListPair.unzip
                                  |>> apfst ListPair.unzip

      val t = \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free ar\<close>\<close>

      val cnj' = HOLogic.mk_list \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close> ts
               |> curry HOLogic.mk_eq (Free ar);

      val cnj = fold mk_conj cnjs cnj'
              |> list_ex vs;
    in
      (((t, ar), SOME cnj), ctxt'')
    end
  | mk_inv_term ctxt (Const (\<^const_name>\<open>SType.DArray\<close>, _) $ dtype) = 
    let
      val da = (singleton (Name.variants (Variable.names_of ctxt)) "da", HOLogic.listT \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>);
      val ctxt' = Variable.declare_names (Free da) ctxt;
      val (((t, (fname, ftyp)), cnj), ctxt'') = mk_inv_term ctxt' dtype;
      val t' = \<^Const>\<open>storage_data.Array \<^Type>\<open>valtype a\<close> for \<open>Free da\<close>\<close>
      val y = (singleton (Name.variants (Variable.names_of ctxt'')) "y", \<^typ>\<open>nat\<close>);
      val t'' =
        (HOLogic.mk_exists (fname, ftyp,
         mk_conj cnj (HOLogic.mk_eq (\<^Const>\<open>List.nth \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close> for \<open>Free da\<close> \<open>Free y\<close>\<close>, t))))
      val cnj' =
        HOLogic.mk_all (fst y, snd y,
          (HOLogic.mk_imp
            (\<^Const>\<open>Orderings.ord_class.less \<^typ>\<open>nat\<close> for \<open>Free y\<close> \<^Const>\<open>size \<open>HOLogic.listT \<^Type>\<open>Stores.storage_data \<^Type>\<open>valtype a\<close>\<close>\<close> for \<open>Free da\<close>\<close>\<close>,
            t'')));
    in
      (((t', da), SOME cnj'), ctxt'')
    end
  | mk_inv_term _ t = error ("unsupported type" ^ @{make_string} t)

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
              fun go mname (((trm, (fname, ftyp)), cnj), ctxt) = ((mname, ((trm, (fname, ftyp)), cnj)), ctxt);
            in
              lthy |> Variable.declare_constraints var
                   |> fold_map (fn(x,y) => (fn ctxt => go x (mk_inv_term ctxt y))) members
            end;
          val trms =
            let
              fun go (x, ((trm, (fname, ftyp)), cnj)) =
                (HOLogic.mk_exists (fname, ftyp,
                  (mk_conj cnj
                    (HOLogic.mk_eq (x, trm)))))
            in
              map go trms'
            end;

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