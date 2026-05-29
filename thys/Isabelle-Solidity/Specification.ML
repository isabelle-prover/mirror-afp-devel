(*  Title:      Specification.ML
    Author:     Diego Marmsoler
*)

signature SOLIDITY_SPEC =
sig

end

structure Solidity_Spec: SOLIDITY_SPEC =
struct
open Solidity_Util
open Solidity_Data

val _ = let
  val specparser =
    let
      fun create_locale (name, variables, payable, constr_params, constr_memory, constr_body, methods, cT, cterms, casex, thy) =
        let
          val internals = filter (fn x => not (fst (snd (fst (fst (fst (fst x))))))) methods
                        |> map (Binding.name_of o fst o fst o fst o fst o fst);

          fun mk_inits f = fold_rev (f #> mk_Bind)

          val name_lc = decapitalizeFirst (Binding.name_of name);
          val name_ct = instantiate_b_a cT;
          val sm_ord = \<^Const>\<open>sm_ord rvalueT exT stateT\<close>
          val fun_sm_ord = \<^Const>\<open>fun_ord smonadT smonadT name_ct for sm_ord\<close>
          val top = \<^Const>\<open>top \<^Type>\<open>set \<^Type>\<open>fun name_ct smonadT\<close>\<close>\<close>
          val mono_sm = \<^Const>\<open>monotone_on \<^Type>\<open>fun name_ct smonadT\<close> smonadT for top fun_sm_ord sm_ord\<close>

          fun mk_constructor ctxt =
            let
              fun mk_default par = \<^Const>\<open>sdefault a for par\<close>

              fun mk_init_storages body =
                let
                  fun go (name, par) = mk_default par
                                    |> mk_init_storage name
                                    |> mk_Bind
                in
                  fold_rev go variables body
                end;
              val ((pl, ml), _) =
                Variable.names_of ctxt
                |> fold_map (mk_valtype_term NONE) constr_params
                ||>> fold_map (mk_valtype_term (SOME true)) constr_memory;
              val (parlist,constr_params') = split_list pl;
              val (memlist,constr_memory') = split_list ml;
              val parlist_free = map Free parlist;
              val memlist_free = map Free memlist;
              val constr_name = constructor_binding (Binding.pos_of name);
              val constr_def_name = Thm.def_binding constr_name;
              val constr_body = Syntax.parse_term ctxt constr_body
                                |> change_transfers name_ct (call name_ct)
                                |> change_externals name_ct (call name_ct)
                                |> Syntax.check_term ctxt
                                |> change_types
                                |> mk_inits mk_write constr_memory'
                                |> mk_inits mk_init constr_params'
                                |> mk_Bind mk_newMemory
                                |> mk_Bind mk_newStack
                                |> mk_init_storages
                                |> mk_Bind (if payable then init_balance else init_balance_np)
                                |> mk_exc
                                |> fold_rev lambda memlist_free
                                |> fold_rev lambda parlist_free
                                |> lambda (call name_ct)

              fun mk_mono (f, f_def, ctxt) =
                let
                  val goal =
                    list_comb (f $ (call name_ct), parlist_free @ memlist_free)
                    |> lambda (call name_ct)
                    |> curry (op $) mono_sm
                    |> HOLogic.mk_Trueprop;
                  val plist_names = map fst (parlist @ memlist);
                  val mono_tac = asm_full_simp_tac (ctxt addsimps (f_def :: (Proof_Context.get_thms ctxt ("mono"))))
                  val thm = Goal.prove ctxt plist_names [] goal (K (mono_tac 1))
                  val mono_name = mono_binding constr_name;
                in
                  Local_Theory.note ((mono_name, @{attributes [partial_function_mono]}), [thm]) ctxt
                end

              fun export (((f,f_name, f_def), (thm_name, thm)), lthy_old) lthy_new =
                let
                  val pi = Proof_Context.export_morphism lthy_old lthy_new;
                  val f_new = Morphism.term pi f;
                  val f_def_new = Morphism.thm pi f_def;
                  val thm_new = Morphism.thm pi thm;
                  val parlist = ListPair.zip (parlist, map snd constr_params);
                  val memlist = ListPair.zip (memlist, map snd constr_memory);
                in
                  (((f_new, parlist, memlist, f_name, f_def_new), (thm_name, thm_new)), lthy_new)
                end;
            in
              ctxt |> tap (K (writeln "Generating constructor definitions ..."))
                   |> Local_Theory.begin_nested |> snd
                   |> Local_Theory.define ((constr_name, NoSyn), ((constr_def_name, []), constr_body))
                   |> tap (K (writeln "Proving constructor monotonicity ..."))
                   |> (fn ((f, (f_name, f_def)), lthy) => mk_mono (f, f_def, lthy)
                   |> (fn ((thm_name,ts),lthy') => Local_Theory.end_nested lthy'
                   |> export (((f, f_name, f_def), (thm_name, single ts)), lthy')))
            end
  
          fun mk_methods ctxt =
            let
              fun mk_method (((((name, (external, payable)), parlist), memlist), cdlist), body) ctxt =
                let
                  val _ = Pretty.writeln (pretty_terms ctxt (map snd parlist))
                  val (((pl, ml), cl), _) =
                    Variable.names_of ctxt
                    |> fold_map (mk_valtype_term NONE) parlist
                    ||>> fold_map (mk_valtype_term (SOME true)) memlist
                    ||>> fold_map (mk_valtype_term (SOME false)) cdlist;
                  val (parlist_f,parlist') = split_list pl;
                  val (memlist_f,memlist') = split_list ml;
                  val (cdlist_f,cdlist') = split_list cl;
                  val parlist_free = map Free parlist_f;
                  val memlist_free = map Free memlist_f;
                  val cdlist_free = map Free cdlist_f;
                  val def_name = Thm.def_binding name
                  val def_body = Syntax.parse_term ctxt body
                                |> change_transfers name_ct (call name_ct)
                                |> change_externals name_ct (call name_ct)
                                |> change_internals name_ct internals cterms
                                |> Syntax.check_term ctxt
                                |> change_types
                                |> (if external then mk_inits mk_cinit cdlist' else I)
                                |> (if external then mk_inits mk_write memlist' else I)
                                |> mk_inits mk_init parlist'
                                |> (if external then mk_Bind mk_newCalldata else I)
                                |> (if external then mk_Bind mk_newMemory else I)
                                |> mk_Bind mk_newStack
                                |> mk_Bind (if payable then init_balance else init_balance_np)
                                |> mk_exc
                                |> fold_rev lambda cdlist_free
                                |> fold_rev lambda memlist_free
                                |> fold_rev lambda parlist_free
                                |> lambda (call name_ct)

                  fun mk_mono (f, f_def, ctxt) =
                    let
                      val goal =
                        list_comb (f $ (call name_ct), parlist_free @ memlist_free @ cdlist_free)
                        |> lambda (call name_ct)
                        |> curry (op $) mono_sm
                        |> HOLogic.mk_Trueprop;
                      val plist_names = map fst (parlist_f @ memlist_f @ cdlist_f);
                      val mono_tac = asm_full_simp_tac (ctxt addsimps (f_def :: (Proof_Context.get_thms ctxt ("mono"))))
                      val thm = Goal.prove ctxt plist_names [] goal (K (mono_tac 1))
                      val mono_name = mono_binding def_name;
                    in
                      Local_Theory.note ((mono_name, @{attributes [partial_function_mono]}), [thm]) ctxt
                    end

                fun export (((f,f_name,f_def), (thm_name, thm)), lthy_old) lthy_new =
                  let
                    val pi = Proof_Context.export_morphism lthy_old lthy_new;
                    val f_new = Morphism.term pi f;
                    val f_def_new = Morphism.thm pi f_def;
                    val thm_new = Morphism.thm pi thm;
                    val parlist_f = ListPair.zip (parlist_f, map snd parlist);
                    val memlist_f = ListPair.zip (memlist_f, map snd memlist);
                    val cdlist_f = ListPair.zip (cdlist_f, map snd cdlist);
                  in
                    (((f_new, name, external, payable, parlist_f, memlist_f, cdlist_f, f_name, f_def_new), (thm_name, thm_new)), lthy_new)
                  end;

                in
                  ctxt |> tap (K (writeln "Generating method definition ..."))
                       |> Local_Theory.begin_nested |> snd
                       |> Local_Theory.define ((name, NoSyn), ((def_name, []), def_body))
                       |> tap (K (writeln "Proving method monotonicity ..."))
                       |> (fn ((f, (f_name, f_def)), lthy) => mk_mono (f, f_def, lthy)
                       |> (fn ((thm_name,ts),lthy') => Local_Theory.end_nested lthy'
                       |> export (((f,f_name,f_def), (thm_name, single ts)), lthy')))
                end
              in
                ctxt |> fold_map mk_method methods
              end
  
          fun mk_partial_function (((con_trm, _, _), _), (ms, ctxt)) =
            let
              fun mkcase ((t, _, _, _, plist, mlist, clist, _, _), _) =
                let
                  val parlist = map (fst #> snd) (plist @ mlist @ clist)
                in
                  (t $ (call name_ct), parlist ---> smonadT)
                end
              val contract = instantiate_b_a cT;
              val cases = map mkcase ms
              val case_t = instantiate_4 casex

              val x = Free ("x",contract)
              val lhs = (list_comb (case_t, con_trm $ (call name_ct) :: map fst cases)) $ x;
              val rhs = (call name_ct) $ x
              val vars = [(Binding.make (pfun_name, \<^here>),NONE,NoSyn)]
              val mprop = \<^Const>\<open>HOL.eq smonadT for rhs lhs\<close>
                        |> HOLogic.mk_Trueprop

              fun export ((term, thm), (lthy_new, lthy_old)) =
                let
                  val pi = Proof_Context.export_morphism lthy_old lthy_new;
                  val term_new = Morphism.term pi term;
                  val thm_new = Morphism.thm pi thm;
                  val induct = Proof_Context.get_thm lthy_new (pfun_name^".raw_induct");
                in
                  ((term_new, thm_new, induct), lthy_new)
                end;
            in
              ctxt
              |> tap (K (writeln "Generating partial function ..."))
              |> Local_Theory.begin_nested |> snd (*Needed?*)
              |> Partial_Function.add_partial_function "sm" vars (Binding.empty_atts,mprop)
              ||> `Local_Theory.end_nested
              |> export
            end
  
          fun mk_locale thy =
            tap (K (writeln "Generating contract locale ..."))
            Expression.add_locale (Binding.name name_lc) Binding.empty [] ([("Solidity.Solidity",(("",false), (Expression.Positional [],[])))],[]) [Element.Constrains [("external", mk_external_t name_ct)]] thy
        in
          thy |> mk_locale
              |> (fn (lname, lthy) => mk_constructor lthy
              ||> mk_methods
              |> (fn (((con_trm, con_parlist, con_memlist, con_name, con_thm), (mono_name, mono_thm)), (ms, lthy')) => mk_partial_function (((con_trm, con_parlist @ con_memlist, con_thm), (mono_name, mono_thm)), (ms, lthy'))
              |> (fn ((pt, pthm, pinduct), lthy'') => Local_Theory.exit_global lthy''
              |> (fn thy' => ((lname, con_trm, payable, con_parlist, con_memlist, con_name, con_thm, mono_name, mono_thm, ms, pt, pthm, pinduct, variables), thy')))))
        end

      fun mk_contract ((name, variables), ((((payable, constr_params), constr_memory), constr_body), methods)) thy =
        let
          fun change_types3 ctxt (((((name, (external, payable)), parlist), memlist), cdlist), body) =
            let
              val parlist = map (apply2 (Syntax.read_term ctxt)) parlist;
              val memlist =
                if not external andalso not (null memlist) then
                  error "only external methods can have memory parameter"
                else
                  map (apply2 (Syntax.read_term ctxt)) memlist;
              val cdlist =
                if not external andalso not (null cdlist) then
                  error "only external methods can have calldata parameter"
                else
                  map (apply2 (Syntax.read_term ctxt)) cdlist;
            in
              (((((name, (external, payable)), parlist), memlist), cdlist), body)
            end;

          val name_lc = decapitalizeFirst (Binding.name_of name);
          val ctxt = Proof_Context.init_global thy; (*TODO: disjoined if needed*)
          val variables = map (apply2 (Syntax.read_term ctxt)) variables;
          val constr_params = map (apply2 (Syntax.read_term ctxt)) constr_params;
          val constr_memory = map (apply2 (Syntax.read_term ctxt)) constr_memory;
          val methods = map (change_types3 ctxt) methods;

          val mk_contract_datatype =
            let
              fun go mem (_, par) = mk_valtype mem par;
              val cparlist = map (go NONE) constr_params @ map (go (SOME true)) constr_memory;
              fun mk_constructor (((((name, _), parlist), memlist), cdlist), _) =
                let
                  val parlist = map (go NONE) parlist @ map (go (SOME true)) memlist @ map (go (SOME false)) cdlist;
                in
                  (parlist, mk_dt_con_name (Binding.name_of name))
                end
              val constructors = (cparlist, mk_dt_con_name con_name) :: map mk_constructor methods;
              val name_contract_datatype = Binding.make (name_lc, Binding.pos_of name);
              fun terms lthy = 
                let
                  val cT = #T (the (BNF_FP_Def_Sugar.fp_sugar_of lthy (mk_global_name lthy name_lc)));
                  val ct = #ctrs (#ctr_sugar (#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of lthy (mk_global_name lthy name_lc)))));
                  val casex = (#casex (#ctr_sugar (#fp_ctr_sugar (the (BNF_FP_Def_Sugar.fp_sugar_of lthy (mk_global_name lthy name_lc))))))
                in
                  ((cT, ct, casex, the (BNF_FP_Def_Sugar.fp_sugar_of lthy (mk_global_name lthy name_lc))), lthy)
                end;
            in
              tap (K (writeln "Generating contract datatype ..."))
              Local_Theory.begin_nested #> snd
              #> define_simple_datatype ([(b, address)], name_contract_datatype) constructors
              #> Local_Theory.end_nested
              #> terms
            end;

          fun register name c ct casex ((lname, con_trm, payable, con_parlist, con_memlist, con_name, con_thm, mono_name, mono_thm, ms, pt, pthm, pinduct, variables), thy) =
            let
              val con_data = {term = con_trm, payable = payable, binding = Binding.empty, name = con_name, def = con_thm, parlist = con_parlist, memlist = con_memlist, mono_name=mono_name, mono=mono_thm, dt_const = hd ct};

              fun go (((t, binding, external, payable, plist, mlist, clist, name, def), (mono_name, mono)), con) =
                (Binding.name_of binding, {term = t, external = external, payable = payable, binding = binding, name = name, def=def, parlist = plist, memlist = mlist, cdlist = clist, mono_name=mono_name, mono=mono, dt_const = con});
              val met_data = map go (ListPair.zip (ms, tl ct)); (*Add some checks for zip*)
            in
              mupdateN name {dt_type = c, dt_cases = casex, locale = lname, members = variables, constructor = con_data, methods = met_data, pfun_name = pt, pfun = pthm, pinduct = pinduct} thy
            end
        in
          thy |> Named_Target.theory_init
              |> mk_contract_datatype
              ||> Local_Theory.exit_global
              |> (fn ((c, ct, casex, _), thy') =>
                    create_locale (name, variables, payable,
                      constr_params, constr_memory, constr_body, methods, c, ct, casex, thy')
              |> register name_lc c ct casex)
        end

      val parameter_parser = Parse.term -- (Parse.$$$ ":" |-- Parse.term);
      val storage_list_parser = Scan.optional (Parse.$$$ "for" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
      val parameter_list_parser = Scan.optional (Parse.$$$ "param" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
      val memory_list_parser = Scan.optional (Parse.$$$ "memory" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
      val calldata_list_parser = Scan.optional (Parse.$$$ "calldata" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
      val body_parser = Parse.$$$ "where" |-- Parse.!!! Parse.term;
      val payable_parser = Scan.optional (Parse.$$$ "payable" >> K true) false;
      val external_parser = Scan.optional (Parse.$$$ "external" >> K true) false;
      val method_parser = Parse.$$$ "cfunction" |-- (Parse.binding -- (external_parser -- payable_parser) -- parameter_list_parser -- memory_list_parser -- calldata_list_parser -- body_parser)
      val constructor_parser = Parse.$$$ "constructor" |-- (payable_parser -- parameter_list_parser -- memory_list_parser -- body_parser)
      val contract_parser = (Parse.binding -- storage_list_parser) -- (constructor_parser -- (Parse.list method_parser))
    in
      contract_parser >> mk_contract
    end
in
  solidity_command Toplevel.theory @{command_keyword "contract"} "creates a contract" specparser
end

end