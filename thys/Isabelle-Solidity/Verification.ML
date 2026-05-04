(*  Title:      Verification.ML
    Author:     Diego Marmsoler
*)

signature SOLIDITY_VERIFICATION =
sig

end

structure Solidity_Verification: SOLIDITY_VERIFICATION =
struct
open Solidity_Util
open Solidity_Data

val _ = let
    fun mk_vcond data ct conpre conpost prepost invs lthy =
      let
        val cdata = #constructor data;
        val frees = map Free (#parlist cdata @ #memlist cdata);
        val post_f = list_comb (conpost, frees);
        val pre_f = list_comb (conpre, frees);
        val err_cond = mk_True;
        val constr = HOLogic.mk_imp (pre_f $ s, post_t $ s $ r $ invs $ err_cond $ post_f)
                     |> fold_rev lambda frees
        fun mkcase (name, mdata) =
          let
            val (pre, post) = lookup_safe prepost name;
            val frees = map Free (#parlist mdata @ #memlist mdata @ #cdlist mdata);
            val post_f = list_comb (post, frees);
            val pre_f = list_comb (pre, frees);
            val inv_cond = if #external mdata then invs else mk_True;
            val err_cond = if #external mdata then invs else mk_True;
            val post_cond = post_t $ s $ r $ inv_cond $ err_cond $ post_f;
          in
            (if #external mdata then
              HOLogic.mk_imp (HOLogic.mk_conj ((mk_inv_state invs $ s), pre_f $ s), post_cond)
            else
              HOLogic.mk_imp (pre_f $ s, post_cond))
            |> fold_rev lambda frees
          end
        val cases = map mkcase (#methods data);

        val case_t = instantiate_3 (#dt_cases data)
        val x = Free ("x", ct)
        val rhs = list_comb (case_t, constr::cases) $ x
        val lhs = Free ("vcond", ct --> stateT --> rT --> @{typ bool}) $ x $ s $ r
        val eq = Logic.mk_equals (lhs, rhs);
        fun export ((vcond_t, (vcond_name, vcond_def)), (lthy_new, lthy_old)) =
          let
            val pi = Proof_Context.export_morphism lthy_old lthy_new;
            val vcond_t_new = Morphism.term pi vcond_t;
            val vcond_def_new = Morphism.thm pi vcond_def;
          in
            ((vcond_t_new, vcond_name, vcond_def_new), lthy_new)
          end;
      in
        tap (K (writeln "Generating verification condition ..."))
        Local_Theory.begin_nested lthy |> snd
        |> Specification.definition {verbose = false} NONE [] [] (Binding.empty_atts, eq)
        ||> `Local_Theory.end_nested
        |> export
      end

    fun mk_vcond_lemmas data vcond vcond_def conpre conpost prepost invs lthy =
      let
        val cdata = #constructor data;
        val constr = instantiate_b_a2 (#dt_const cdata);
        val frees = map Free (#parlist cdata @ #memlist cdata);
        val names = map (dest_Free #> fst) frees;
        val post_f = list_comb (conpost, frees);
        val pre_f = list_comb (conpre, frees);
        val err_cond = mk_True;
        val lem = HOLogic.mk_Trueprop (HOLogic.mk_eq (vcond $ list_comb (constr, frees) $ s $ r, HOLogic.mk_imp (pre_f $ s, post_t $ s $ r $ invs $ err_cond $ post_f)));
        val thm = Goal.prove lthy ("s"::"r"::names) [] lem (fn {context, ...} => (rewrite_goal_tac context [vcond_def] THEN' Goal.conjunction_tac) 1 THEN auto_tac context);

        fun mkcase (name, mdata) sum =
          let
            val constr = instantiate_b_a2 (#dt_const mdata);
            val frees = map Free (#parlist mdata @ #memlist mdata @ #cdlist mdata);
            val names = map (dest_Free #> fst) frees;
            val (pre, post) = lookup_safe prepost name;
            val post_f = list_comb (post, frees);
            val pre_f = list_comb (pre, frees);
            val inv_cond = if #external mdata then invs else mk_True;
            val err_cond = if #external mdata then invs else mk_True;
            val post_cond = post_t $ s $ r $ inv_cond $ err_cond $ post_f;
            val rhs = if #external mdata then HOLogic.mk_imp (HOLogic.mk_conj (mk_inv_state invs $ s, pre_f $ s), post_cond) else HOLogic.mk_imp (pre_f $ s, post_cond);
          in
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (vcond $ list_comb (constr, frees) $ s $ r, rhs)), sum @ names)
          end;
        val (lems, frees) = fold_map mkcase (#methods data) [];

        val frees = rmdup frees;
        val thms = Goal.prove_common lthy NONE ("s"::"r"::frees) [] lems (fn {context, ...} => (rewrite_goal_tac context [vcond_def] THEN' Goal.conjunction_tac) 1 THEN auto_tac context);
        fun export ((name, thms), (lthy_new, lthy_old)) =
          let
            val pi = Proof_Context.export_morphism lthy_old lthy_new;
            val thms_new = map (Morphism.thm pi) thms;
          in
            ((name, thms_new), lthy_new)
          end;
      in
        tap (K (writeln "Generating vcond lemmas ..."))
        Local_Theory.begin_nested lthy |> snd
        |> Local_Theory.note ((@{binding vcond}, []), thm::thms)
        ||> `Local_Theory.end_nested
        |> export
      end;

    fun verify pi call mdata name_ct inv_name vcond vcond_thm induct rules ctxt =
      let
        val defs = map (snd #> #def #> Morphism.thm pi) mdata
        val (crule,mrules) = flat rules |> hd_tl

        fun select_tac context (t,i) =
          let
            val concl = t |> Logic.strip_assums_concl |> HOLogic.dest_Trueprop
            val _ = Pretty.writeln (pretty_terms ctxt [t]);
          in
            case concl of
              (*strict*)
              Const (\<^const_name>\<open>Solidity.Contract.post\<close>, _) $ _ $ _ $ _ $ _ $ (Const (\<^const_name>\<open>Utils.K\<close>, _) $ Const (\<^const_name>\<open>False\<close>, _)) $ _  => (eresolve_tac context (flat rules) THEN_ALL_NEW force_tac (ctxt |> Simplifier.add_simps defs)) i
              (*internal*)
            | Const (\<^const_name>\<open>Solidity.Contract.post\<close>, _) $ _ $ _ $ _ $ (Const (\<^const_name>\<open>Utils.K\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _)) $ (Const (\<^const_name>\<open>Utils.K\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _)) $ _  => (eresolve_tac context (flat rules) THEN_ALL_NEW force_tac (ctxt |> Simplifier.add_simps defs)) i
              (*constructor*)
            | Const (\<^const_name>\<open>Solidity.Contract.post\<close>, _) $ _ $ _ $ _ $ _ $ (Const (\<^const_name>\<open>Utils.K\<close>, _) $ Const (\<^const_name>\<open>True\<close>, _)) $ _  => (eresolve_tac context [crule] THEN_ALL_NEW force_tac (ctxt |> Simplifier.add_simps defs)) i
              (*external*)
            | Const (\<^const_name>\<open>Solidity.Contract.post\<close>, _) $ _ $ _ $ _ $ _ $ _ $ _  => (resolve_tac context [@{thm Contract.post_true}] THEN' force_tac (ctxt |> Simplifier.add_simps defs) THEN' force_tac (ctxt |> Simplifier.add_simps defs) THEN' eresolve_tac context mrules THEN_ALL_NEW force_tac (ctxt |> Simplifier.add_simps defs)) i
            | _ => (K no_tac) i
          end;

        fun call_tac ctxt asm =
          resolve_tac ctxt [induct]
          THEN' Induct_Tacs.case_tac ctxt "x" [] NONE
          THEN' (fn _ => auto_tac (ctxt |> Simplifier.del_simps @{thms K.simps} |> Simplifier.add_simps vcond_thm))
          THEN' REPEAT o (SUBGOAL (select_tac ctxt))
          THEN' cut_facts_tac asm
          THEN' assume_tac ctxt

        val (_, ctxt') = Variable.add_fixes ["x", "s", "r"] ctxt
        val x = Free ("x", name_ct);
        val asm = HOLogic.mk_Trueprop (effect $ (call $ x) $ s $ r);
        val conc = HOLogic.mk_Trueprop (vcond $ x $ s $ r);
        val thm = Goal.prove ctxt' [] [asm] conc (fn {prems, context, ...} => call_tac context prems 1)
                |> singleton (Proof_Context.export ctxt' ctxt)
      in
        Local_Theory.note ((inv_name, []), [thm]) ctxt' |> snd |> Local_Theory.exit
      end

    fun mk_locale data name_lc vcond invs name_ct ct thy =
      let
        val inv = @{term Contract.inv};
        val invs' = lambda s' ((mk_inv_state invs) $ s');
        
        val x = Free ("x", ct);
        val h = Free ("h", stateT);
        
        val assumption =
          Logic.all s
            (Logic.mk_implies
              (HOLogic.mk_Trueprop
                (HOLogic.mk_all ("x", ct,
                  HOLogic.mk_all ("h", stateT,
                    HOLogic.mk_all ("r", rT,
                      HOLogic.mk_imp
                        (effect $ ((call name_ct) $ x) $ h $ r
                        ,vcond $ x $ h $ r)))))
              ,HOLogic.mk_Trueprop
                (HOLogic.mk_all
                  ("r", rT, HOLogic.mk_imp
                    (HOLogic.mk_conj
                      (effect $ (mk_external ct $ (call name_ct)) $ s $ r
                      , (mk_inv_state invs) $ s)
                    , inv $ r $ invs' $ invs')))))

        val binding = Binding.name (name_lc ^ "_external");
      in
        tap (K (writeln "Generating verification locale ..."))
        Expression.add_locale binding Binding.empty [] ([(#locale data,(("",true), (Expression.Positional [],[])))],[]) [Element.Assumes [((@{binding "external_inv"}, []), [(assumption, [])])]] thy
      end

    fun mk_proof data lname inv_name vcond vcond_thms name_ct ct conpre conpost prepost invs lthy =
      let
        val cdata = #constructor data;

        val pi = Proof_Context.theory_of lthy |> get_morphism (#locale data) lname;
        val vcond_thms' = map (Morphism.thm pi) vcond_thms;
        val induct = Morphism.thm pi (#pinduct data)

        val frees = map Free (#parlist cdata @ #memlist cdata);
        val post_f = list_comb (conpost, frees);
        val pre_f = list_comb (conpre, frees);
        val err_cond = mk_True;

        val x = Free ("x", ct);
        val h = Free ("h", stateT);
        val vcond' = Logic.all x (Logic.all h (Logic.all r (Logic.mk_implies (HOLogic.mk_Trueprop (effect $ ((call name_ct) $ x) $ h $ r),  HOLogic.mk_Trueprop (vcond $ x $ h $ r)))));
        
        val lem =
          [(Logic.all (call name_ct)
            (Logic.mk_implies
              (HOLogic.mk_Trueprop (effect $ list_comb (#term cdata $ (call name_ct), frees) $ s $ r)
              ,Logic.mk_implies
                (vcond'
                ,Logic.mk_implies
                  (HOLogic.mk_Trueprop (pre_f $ s)
                  ,HOLogic.mk_Trueprop (post_t $ s $ r $ invs $ err_cond $ post_f))))),[])]

        fun mkcase (name, mdata) =
          let
            val frees = map Free (#parlist mdata @ #memlist mdata @ #cdlist mdata);
            val (pre, post) = lookup_safe prepost name;
            val post_f = list_comb (post, frees);
            val pre_f = list_comb (pre, frees);
            val inv_cond = if #external mdata then invs else mk_True;
            val err_cond = mk_True;

            val x = Free ("x", ct);
            val h = Free ("h", stateT);
            val callx = (call name_ct) $ x;
            val vcond' = Logic.all x (Logic.all h (Logic.all r (Logic.mk_implies (HOLogic.mk_Trueprop (effect $ callx $ h $ r),  HOLogic.mk_Trueprop (vcond $ x $ h $ r)))));
            val post_cond = HOLogic.mk_Trueprop (post_t $ s $ r $ inv_cond $ err_cond $ post_f);
            val rhs =
              if #external mdata then
                Logic.mk_implies (HOLogic.mk_Trueprop ((mk_inv_state invs) $ s), post_cond)
              else
                post_cond;
          in
            [(Logic.all (call name_ct)
              (fold Logic.all frees
                (Logic.mk_implies
                  (HOLogic.mk_Trueprop (effect $ list_comb (#term mdata $ (call name_ct), frees) $ s $ r)
                  ,Logic.mk_implies
                    (vcond'
                    ,Logic.mk_implies
                      (HOLogic.mk_Trueprop (pre_f $ s)
                      ,rhs))))),[])]
          end;
        val lems = map mkcase (#methods data);
      in
        tap (K (writeln "Proving theorem"))
        Proof.theorem NONE (verify pi (#pfun_name data) (#methods data) name_ct inv_name vcond vcond_thms' induct) (lem::lems) lthy
      end;

    fun mk_wp_rule vcond name_ct ct invs lthy =
      let
        fun proof_tac {prems, context} =
          let
            val vars = Vars.make1 ((("s", 0), stateT), Thm.cterm_of context s);

            val external_inv = (Proof_Context.get_thm context "external_inv" OF [hd prems])
                               |> Thm.instantiate (TVars.empty, vars)
            val simps = [@{thm wp_def}
                        ,@{thm Contract.inv_def}
                        ,@{thm effect_def}]
                        @(tl prems)
          in
            cut_facts_tac [external_inv] 1
            THEN auto_tac (Splitter.add_split @{thm result.split} (context |> Simplifier.add_simps simps))
          end

        val call = call name_ct
        val x = Free ("x", ct);
        val h = Free ("h", stateT);
        val assumption1 =
          HOLogic.mk_Trueprop
            (HOLogic.mk_all ("x", ct,
              HOLogic.mk_all ("h", stateT,
                HOLogic.mk_all ("r", rT,
                  HOLogic.mk_imp
                    (effect $ (call $ x) $ h $ r
                    ,vcond $ x $ h $ r)))));

        val assumption2 = HOLogic.mk_Trueprop ((mk_inv_state invs) $ s);

        val P = Free ("P", rvalueT --> stateT --> @{typ bool})
        val Q = Free ("Q", exT --> stateT --> @{typ bool})

        val x = Free ("x", rvalueT)
        val assumption3 = Logic.all s
                            (Logic.all x
                              (Logic.mk_implies
                                (HOLogic.mk_Trueprop ((mk_inv_state invs) $ s)
                                ,HOLogic.mk_Trueprop (P $ x $ s))));

        val x = Free ("x", exT)
        val assumption4 = Logic.all s
                            (Logic.all x
                              (Logic.mk_implies
                                (HOLogic.mk_Trueprop ((mk_inv_state invs) $ s)
                                ,HOLogic.mk_Trueprop (Q $ x $ s))));

        val wp = \<^Const>\<open>wp rvalueT exT stateT\<close>;
        val goal = HOLogic.mk_Trueprop (wp $ (Free ("external", mk_external_t name_ct) $ call) $ P $ Q $ s);

        val (_, ctxt) = Variable.add_fixes ["s", "call", "P", "Q"] lthy

        val thm = Goal.prove ctxt [] [assumption1, assumption2, assumption3, assumption4] goal proof_tac
                |> singleton (Proof_Context.export ctxt lthy);
      in
        tap (K (writeln "Generating wp rule ..."))
        Local_Theory.note ((@{binding wp_external}, @{attributes [wprules]}), [thm]) lthy
      end

    fun verify_invariant (inv_name, (((invariant, (conpre, conpost)), prepost), contract_name)) thy =
      let
        val name_lc = decapitalizeFirst contract_name;
        val lthy = Named_Target.init [] (Context.theory_base_name thy ^ "." ^ name_lc) thy
        val data = the (mlookupN (Proof_Context.theory_of lthy) name_lc);

        val tp = HOLogic.mk_prodT (\<^typ>\<open>String.literal\<close> --> \<^Type>\<open>storage_data \<^Type>\<open>valtype a\<close>\<close>, \<^typ>\<open>nat\<close>) --> \<^typ>\<open>bool\<close>
        val invariant = readAs lthy tp invariant;

        val m = #constructor data;
        val parlist = map snd (#parlist m @ #memlist m);
        val tp = parlist ---> stateT --> \<^typ>\<open>bool\<close>;
        val conpre = readAs lthy tp conpre;
        val tp = parlist ---> stateT --> rvalueT --> stateT --> \<^typ>\<open>bool\<close>;
        val conpost = readAs lthy tp conpost;

        fun go (name, (pre, post)) =
          let
            val m = lookup_safe (#methods data) name;
            val parlist = map snd (#parlist m @ #memlist m @ #cdlist m);
            val tp = parlist ---> stateT --> \<^typ>\<open>bool\<close>;
            val pre = readAs lthy tp pre;
            val tp = parlist ---> stateT --> rvalueT --> stateT --> \<^typ>\<open>bool\<close>;
            val post = readAs lthy tp post;
          in
            cons (name, (pre, post))
          end
        val prepost = fold go prepost [];
        val ct = mk_contract_typ lthy name_lc;
        val name_ct = mk_contract_typ lthy name_lc;
      in
        lthy |> mk_vcond data ct conpre conpost prepost invariant
             |> (fn ((vcond, vcond_name, vcond_def), lthy') => mk_vcond_lemmas data vcond vcond_def conpre conpost prepost invariant lthy'
             ||> Local_Theory.exit_global
             |> (fn ((name, thms), lthy'') => mk_locale data name_lc vcond invariant name_ct ct lthy''
             |> (fn (lname, lthy''') => mk_wp_rule vcond name_ct ct invariant lthy'''
             |> (fn ((wp_name, wp_thm), lthy'''') => mk_proof data lname inv_name vcond thms name_ct ct conpre conpost prepost invariant lthy''''))))
      end
    in
      solidity_command Toplevel.theory_to_proof @{command_keyword "verification"}
      "initiates verification of invariant"
      (Parse.binding -- (Parse.$$$ ":" |-- ((Parse.term -- (Parse.term -- Parse.term) -- (Parse.and_list (Parse.name -- (Parse.term -- Parse.term)))) -- (Parse.$$$ "for" |-- Parse.string))) >> verify_invariant)
    end
end
