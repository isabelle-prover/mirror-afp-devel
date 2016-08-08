theory Scratch
imports "../../Sepref"
  keywords "sepref_decl_op" :: thy_goal
begin






  sepref_decl_op list_empty: "[]" :: "\<langle>A\<rangle>list_rel" .
  sepref_decl_op list_nth: "\<lambda>l i. l!(i)" :: "[\<lambda>(l,i). i<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<rightarrow> A" .
  sepref_decl_op list_swap: "\<lambda>l i j. l[i:=l!j,j:=l!i]" :: "[\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel\<times>\<^sub>rnat_rel)\<times>\<^sub>rnat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .


xxx, ctd here: Wrap-up and test on list-interface!


oops    
  xxx: Operation modes and modifiers:
    Controlling what gets defined:
      no-mop, is-mop: Do not define mop, define specified operation as mop
      no-def: Do not define constant for operation

    Proofs:
      raw-goals: Do not pre-process proof goals
    




context fixes a :: 'a begin

ML \<open>
  val ctxt = @{context}

  val T = Syntax.read_typ ctxt "'b \<Rightarrow> ('b\<times>'a) list" 
  val t = Syntax.read_term ctxt "\<lambda>x. [(x,a)]"
  
  val T = Logic.mk_type T

  val ([T,t],ctxt) = import_terms_disj [T,t] ctxt

  local val new_ctxt = Variable.declare_term T ctxt
  in val T = singleton (Variable.export_terms new_ctxt ctxt) T end

  local val new_ctxt = Variable.declare_term t ctxt
  in val t = singleton (Variable.export_terms new_ctxt ctxt) t end

  (*val ([T,t],ctxt) = Variable.import_terms true [T,t] ctxt*)

  val (T,ctxt) = yield_singleton (Variable.import_terms true) T ctxt
  val (t,ctxt) = yield_singleton (Variable.import_terms true) t ctxt



\<close>



oops
xxx: Now integrate with sepref_register! 
  Use the relations to get the interface, by relation\<rightarrow>interface mapping
  Allow optional overriding of interface





  thm mop_list_nth_def



  lemma "pre_list_nth (x,y) \<Longrightarrow> mop_list_nth x y \<le> uncurry (RETURN \<circ>\<circ> op_list_nth) (x,y)"
    unfolding mop_list_nth_def curry_conv 
    apply (erule mop_spec_rl)
    done
    
    
term "uncurry mop_list_nth"
thm mop_list_nth_def[unfolded curry_shl]

lemma le_RETURN_eq_le_SPEC: "m \<le> RETURN x \<longleftrightarrow> m \<le> SPEC (\<lambda>r. r=x)" by (auto simp: pw_le_iff refine_pw_simps)


  ML \<open>


    val ctxt = @{context}
    val mop_def_thm = @{thm mop_list_nth_def}
    val Ts = [@{typ "'x list"}, @{typ "nat"}]

    val orig_ctxt = ctxt
    val ctxt = Variable.declare_thm mop_def_thm ctxt
    val ctxt = fold Variable.declare_typ Ts ctxt

    val (x,ctxt) = fix_left_tuple_from_Ts "x" Ts ctxt
                   
    val mop_def_thm = mop_def_thm
      |> Local_Defs.unfold ctxt @{thms curry_shl}
    
    val thm = (@{thm mop_spec_rl_from_def} OF [mop_def_thm])
      |> Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt x)]
      |> Local_Defs.unfold ctxt @{thms uncurry_apply uncurry0_apply o_apply}
      |> Local_Defs.unfold ctxt @{thms op_list_nth_def pre_list_nth_def Product_Type.split}

    val thm = thm RS @{thm order_trans}  

    val thm = singleton (Variable.export ctxt orig_ctxt) thm

    \<close>  



  ML \<open>


    val ctxt = @{context}
    val mop_def_thm = @{thm mop_list_nth_def}

    val orig_ctxt = ctxt
    val (mop_def_thm,ctxt) = yield_singleton (apfst snd oo Variable.import false) mop_def_thm ctxt

    val (x,ctxt) = fix_left_tuple_from_Ts "x" [@{typ "'b list"}, @{typ "nat"}] ctxt
                   
    val mop_def_thm = mop_def_thm
      |> Local_Defs.unfold ctxt @{thms curry_shl}
    
    val thm = (@{thm mop_spec_rl_from_def} OF [mop_def_thm])
      |> Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt x)]
      |> Local_Defs.unfold ctxt @{thms uncurry_apply uncurry0_apply o_apply}
      |> Local_Defs.unfold ctxt @{thms op_list_nth_def pre_list_nth_def Product_Type.split}

    val thm = thm RS @{thm order_trans}  

    val thm = singleton (Variable.export ctxt orig_ctxt) thm

    \<close>  


  thm mop_spec_rl'[OF mop_list_nth_def[unfolded curry_shl], of "(x,y)", unfolded uncurry_apply o_apply]

  lemma "(uncurry mop_list_nth,uncurry mop_list_nth) \<in> (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<rightarrow>\<^sub>f \<langle>A\<rangle>nres_rel"
    unfolding mop_list_nth_def uncurry_curry_id
    apply (rule param_mopI)
    apply (rule list_nth.param)
    apply (rule list_nth.param_pre)
    done


  thm list_nth.param[folded op_list_nth_def]
  thm op_list_nth_def[THEN meta_eq_to_obj_eq, THEN ext]


end
