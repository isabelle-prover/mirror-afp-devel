header {* Actual Implementation of the CAVA Model Checker *}
theory CAVA_Impl
imports
  "CAVA_Abstract"
  "../CAVA_Automata/Automata_Impl"
  
  "../LTL_to_GBA/LTL_to_GBA_impl" (* LTL to BA *)

  "../Gabow_SCC/Gabow_GBG_Code" (* Gabow's Algorithm *)
  "Nested_DFS/NDFS_SI" (* Nested-DFS, standard-invars formalization *)

  "BoolProgs/BoolProgs"                   (* Boolean Programs *)
  "BoolProgs/Programs/BoolProgs_Programs" (* the actual programs *)
  "BoolProgs/BoolProgs_LTL_Conv"          (* LTL parsing setup *)

  "../Promela/PromelaLTL" (* Promela *)

  "~~/src/HOL/Library/AList_Mapping"
  "../CAVA_Automata/CAVA_Base/CAVA_Code_Target"
begin

(*<*)
subsection {* Exporting Graphs *}

(* TODO: frv_export is going to be replaced by more explicit implementation 
  of graphs.
  For the moment, we just keep it here.
*)
definition "frv_edge_set G \<equiv> frg_E G \<inter> (frg_V G \<times> UNIV)"

definition "frv_edge_set_aimpl G \<equiv> FOREACHi (\<lambda>it r. r = frg_E G \<inter> ((frg_V G - it) \<times> UNIV))
  (frg_V G) 
  (\<lambda>u r. do {
    let E = (\<lambda>v. (u,v))`(succ_of_E (frg_E G) u);
    ASSERT (E \<inter> r = {});
    RETURN (E \<union> r)
  }) 
  {}"

lemma frv_edge_set_aimpl_correct: 
  "finite (frg_V G) \<Longrightarrow> frv_edge_set_aimpl G \<le> SPEC (\<lambda>r. r = frv_edge_set G)"
  unfolding frv_edge_set_aimpl_def frv_edge_set_def
  apply (refine_rcg refine_vcg)
  apply auto []
  apply auto []
  apply (auto simp: succ_of_E_def) []
  apply auto []
  done

schematic_lemma frv_edge_set_impl_aux:
  assumes [autoref_rules]: "(eq,op =)\<in>R \<rightarrow> R \<rightarrow> bool_rel"
  assumes [relator_props]: "single_valued R"
  shows "(?c, frv_edge_set_aimpl) \<in> \<langle>Re,R\<rangle>frgv_impl_rel_ext \<rightarrow> \<langle>\<langle>R \<times>\<^sub>r R\<rangle>list_set_rel\<rangle>nres_rel"
  unfolding frv_edge_set_aimpl_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition frv_edge_set_impl uses frv_edge_set_impl_aux
lemmas [autoref_rules] = frv_edge_set_impl.refine[OF GEN_OP_D PREFER_sv_D]

schematic_lemma frv_edge_set_code_aux: "RETURN ?c \<le> frv_edge_set_impl eq G"
  unfolding frv_edge_set_impl_def by (refine_transfer (post))
concrete_definition frv_edge_set_code for eq G uses frv_edge_set_code_aux
lemmas [refine_transfer] = frv_edge_set_code.refine

lemma frv_edge_set_autoref[autoref_rules]:
  assumes EQ[unfolded autoref_tag_defs]: "GEN_OP eq op = (R \<rightarrow> R \<rightarrow> bool_rel)"
  assumes SV[unfolded autoref_tag_defs]: "PREFER single_valued R"
  shows "(frv_edge_set_code eq,frv_edge_set) \<in> \<langle>Re,R\<rangle>frgv_impl_rel_ext \<rightarrow> \<langle>R \<times>\<^sub>r R\<rangle>list_set_rel"
proof (intro fun_relI)
  fix Gi G
  assume Gr: "(Gi, G) \<in> \<langle>Re, R\<rangle>frgv_impl_rel_ext" 
  hence [simp]: "finite (frg_V G)"
    unfolding frgv_impl_rel_ext_def frg_impl_rel_ext_def
      gen_frg_impl_rel_ext_def
    by (auto simp: list_set_rel_def br_def)

  note frv_edge_set_code.refine
  also note frv_edge_set_impl.refine[OF EQ SV, THEN fun_relD, OF Gr, THEN nres_relD]
  also note frv_edge_set_aimpl_correct
  finally show "(frv_edge_set_code eq Gi, frv_edge_set G) \<in> \<langle>R \<times>\<^sub>r R\<rangle>list_set_rel" 
    by (rule RETURN_ref_SPECD) simp_all
qed

definition "frv_export G \<equiv> do {
  nodes \<leftarrow> SPEC (\<lambda>l. set l = frg_V G \<and> distinct l);
  V0 \<leftarrow> SPEC (\<lambda>l. set l = frg_V0 G \<and> distinct l);
  E \<leftarrow> SPEC (\<lambda>l. set l = frv_edge_set G \<and> distinct l);
  RETURN (nodes,V0,E)
  }"

schematic_lemma frv_export_impl_aux:
  fixes R :: "('vi \<times> 'v) set"
  notes [autoref_tyrel] = TYRELI[where R = "\<langle>R \<times>\<^sub>r R\<rangle>list_set_rel"]
  assumes EQ[autoref_rules]: "(eq,op =)\<in>R \<rightarrow> R \<rightarrow> bool_rel"
  assumes SVR[relator_props]: "single_valued R"
  shows "(?c, frv_export) 
  \<in> \<langle>Re,R\<rangle>frgv_impl_rel_ext 
  \<rightarrow> \<langle>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R \<times>\<^sub>r R\<rangle>list_rel\<rangle>nres_rel"
  unfolding frv_export_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done

concrete_definition frv_export_impl for eq uses frv_export_impl_aux
lemmas [autoref_rules] = frv_export_impl.refine[OF GEN_OP_D PREFER_sv_D]

schematic_lemma frv_export_code_aux: "RETURN ?c \<le> frv_export_impl eq G"
  unfolding frv_export_impl_def
  apply (refine_transfer (post))
  done
concrete_definition frv_export_code for eq G uses frv_export_code_aux
lemmas [refine_transfer] = frv_export_code.refine

(*>*)

subsection {* Setup *}

subsubsection {* LTL to GBA conversion *}

text {* In the following, we set up the algorithms for LTL to GBA conversion. *}

definition is_ltl_to_gba_algo 
  :: "('a ltlc \<Rightarrow> (nat, 'a \<Rightarrow> bool, unit) igbav_impl_scheme) \<Rightarrow> bool"
  -- "Predicate that must be satisfied by an LTL to GBA conversion"
  where 
  "is_ltl_to_gba_algo algo \<equiv> (algo, ltl_to_gba_spec) 
    \<in> ltl_rel 
    \<rightarrow> \<langle>igbav_impl_rel_ext unit_rel nat_rel (\<langle>Id\<rangle>fun_set_rel)\<rangle>plain_nres_rel"

definition gerth_ltl_to_gba 
  -- "Conversion based on Gerth's Algorithm"
  where "gerth_ltl_to_gba \<phi> 
  \<equiv> create_name_igba (ltln_rewrite (ltl_to_ltln (ltl_pushneg (ltlc_to_ltl \<phi>))))"

lemma gerth_ltl_to_gba_refine:
  "gerth_ltl_to_gba \<phi> \<le> \<Down>Id (ltl_to_gba_spec \<phi>)"
  apply simp
  unfolding ltl_to_gba_spec_def gerth_ltl_to_gba_def
  apply (rule order_trans[OF create_name_igba_correct])
  apply (rule SPEC_rule)

  apply (auto simp add: igba.lang_def ltlc_language_def ltln_rewrite__equiv
    ltl_nnf_equiv ltlc_to_ltl_equiv)
  done

definition "gerth_ltl_to_gba_code \<phi> 
  \<equiv> create_name_igba_code 
      (ltln_rewrite (ltl_to_ltln (ltl_pushneg (ltlc_to_ltl \<phi>))))"  
  
lemma gerth_ltl_to_gba_code_refine:
  "is_ltl_to_gba_algo gerth_ltl_to_gba_code"
proof -
  have "\<And>\<phi>. RETURN (gerth_ltl_to_gba_code \<phi>) 
    \<le> \<Down>(igbav_impl_rel_ext unit_rel nat_rel (\<langle>Id\<rangle>fun_set_rel)) 
      (gerth_ltl_to_gba \<phi>)"
    using assms 
    unfolding gerth_ltl_to_gba_def[abs_def] gerth_ltl_to_gba_code_def[abs_def]
    apply (rule order_trans[OF create_name_igba_code.refine])
    apply (rule create_name_igba_impl.refine[THEN fun_relD, THEN nres_relD])
    apply simp
    apply simp
    done
  also note gerth_ltl_to_gba_refine
  finally show ?thesis 
    unfolding is_ltl_to_gba_algo_def 
    by (blast intro: plain_nres_relI)
qed


text {* We define a function that chooses between the possible conversion 
  algorithms. (Currently there is only one) *}
datatype config_l2b = CFG_L2B_GERTHS

definition "ltl_to_gba_code cfg 
  \<equiv> case cfg of CFG_L2B_GERTHS \<Rightarrow> gerth_ltl_to_gba_code"

lemma ltl_to_gba_code_refine:
  "is_ltl_to_gba_algo (ltl_to_gba_code cfg)"
  apply (cases cfg)
  unfolding ltl_to_gba_code_def

  using gerth_ltl_to_gba_code_refine
  apply simp
  done

subsubsection {* Counterexample Search *}
definition is_find_ce_algo 
  :: "(('a, unit)igbg_impl_scheme \<Rightarrow> 'a lasso option option) \<Rightarrow> bool" 
  -- "Predicate that must be satisfied by counterexample search algorithm"
  where
  "is_find_ce_algo algo \<equiv> (algo, find_ce_spec) 
    \<in> igbg_impl_rel_ext unit_rel Id 
  \<rightarrow> \<langle>\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel\<rangle>plain_nres_rel"

definition gabow_find_ce_code 
  -- "Emptiness check based on Gabow's SCC Algorithm"
  where "gabow_find_ce_code
  \<equiv> Option.map (Some o lasso_of_prpl) o Gabow_GBG_Code.find_lasso_tr"

lemma gabow_find_ce_code_refine: "is_find_ce_algo 
  (gabow_find_ce_code 
    :: ('a::hashable, unit) igbg_impl_scheme \<Rightarrow> 'a lasso option option)"
proof -
  have AUX_EQ: 
    "\<And>gbgi::('a, unit) igbg_impl_scheme. RETURN (gabow_find_ce_code gbgi)
    = (do {
      l \<leftarrow> RETURN (find_lasso_tr gbgi);
      RETURN (Option.map (Some \<circ> lasso_of_prpl) l)
    })" by (auto simp: gabow_find_ce_code_def)

  show ?thesis
    (* TODO: Clean up this proof! *)
    unfolding is_find_ce_algo_def 
    apply (intro fun_relI plain_nres_relI)
    unfolding find_ce_spec_def AUX_EQ
    apply (refine_rcg)
    apply (rule order_trans[
      OF bind_mono[OF Gabow_GBG_Code.find_lasso_tr_correct order_refl]])
    apply assumption
    apply assumption
    unfolding igb_graph.find_lasso_spec_def
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (clarsimp simp: lasso_run_rel_sv option_rel_sv split: option.split_asm)
    apply (metis igb_graph.is_lasso_prpl_of_lasso igb_graph.accepted_lasso 
      prod.exhaust)
    apply (simp add: option_rel_def lasso_run_rel_def br_def)
    by (metis igb_graph.is_lasso_prpl_conv igb_graph.lasso_accepted)
qed

definition ndfs_find_ce 
  :: "('q::hashable,_) igb_graph_rec_scheme \<Rightarrow> 'q lasso option option nres" 
  -- "Emptiness check based on nested DFS"
  where 
  "ndfs_find_ce G \<equiv> do {
    ASSERT (igb_graph G);
    let G = igb_graph.degeneralize G;
    l \<leftarrow> blue_dfs G;
    case l of
      None \<Rightarrow> RETURN None
    | Some l \<Rightarrow> do { 
        ASSERT (snd l \<noteq> []); 
        RETURN (Some (Some (map_lasso fst (lasso_of_prpl l)))) 
      }
  }"

lemma ndfs_find_ce_refine: "(G',G)\<in>Id \<Longrightarrow> 
  ndfs_find_ce G' \<le> \<Down>(\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>option_rel\<rangle>option_rel) (find_ce_spec G)"
  apply simp
  unfolding find_ce_spec_def
proof (refine_rcg SPEC_refine_sv refine_vcg)
  assume [simp]: "igb_graph G"
  then interpret igb_graph G .

  have [simp]: "b_graph degeneralize" by (simp add: degen_invar)
  (*then interpret bg!: b_graph degeneralize .*)

  show "ndfs_find_ce G
    \<le>
    (SPEC (\<lambda>res. \<exists>res'. 
         (res,res')\<in>(\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel)
       \<and> (case res' of None \<Rightarrow> \<forall>r. \<not> is_acc_run r
         | Some None \<Rightarrow> Ex is_acc_run 
         | Some (Some x) \<Rightarrow> is_acc_run x)))"
    unfolding ndfs_find_ce_def find_lasso_spec_def ce_correct_def
    apply (refine_rcg refine_vcg order_trans[OF blue_dfs_correct])
    apply (clarsimp_all)

    apply (auto 
      elim!: degen_acc_run_complete[where m="\<lambda>_. ()"]
      dest!: degen.accepted_lasso
      simp: degen.is_lasso_prpl_of_lasso[symmetric] prpl_of_lasso_def
      simp del: degen.is_lasso_prpl_of_lasso) []

    apply (auto 
      simp: b_graph.is_lasso_prpl_def fr_graph.is_lasso_prpl_pre_def) []

    apply (auto split: option.split
      simp: degen.is_lasso_prpl_conv lasso_run_rel_def br_def
      dest: degen.lasso_accepted degen_acc_run_sound
    ) []
    done
qed


schematic_lemma ndfs_find_ce_impl_aux: "(?c, ndfs_find_ce) 
  \<in> igbg_impl_rel_ext Rm Id 
  \<rightarrow> \<langle>
    \<langle>\<langle>\<langle>unit_rel,Id::('a::hashable\<times>_) set\<rangle>lasso_rel_ext\<rangle>option_rel\<rangle>option_rel
  \<rangle> nres_rel"
  unfolding ndfs_find_ce_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (trace, keep_goal))
  done
concrete_definition ndfs_find_ce_impl uses ndfs_find_ce_impl_aux

schematic_lemma ndfs_find_ce_code_aux: "RETURN ?c \<le> ndfs_find_ce_impl G"
  unfolding ndfs_find_ce_impl_def
  by (refine_transfer (post))
concrete_definition ndfs_find_ce_code uses ndfs_find_ce_code_aux


lemma ndfs_find_ce_code_refine: "is_find_ce_algo ndfs_find_ce_code"
  unfolding is_find_ce_algo_def
proof (intro fun_relI plain_nres_relI)
  fix gbgi :: "('a,unit) igbg_impl_scheme" and gbg :: "'a igb_graph_rec"
  assume R: "(gbgi, gbg) \<in> igbg_impl_rel_ext unit_rel Id"
  note ndfs_find_ce_code.refine
  also note ndfs_find_ce_impl.refine[param_fo, THEN nres_relD, OF R]
  also note ndfs_find_ce_refine[OF IdI]
  finally show "RETURN (ndfs_find_ce_code gbgi)
    \<le> \<Down> (\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel) 
      (find_ce_spec gbg)"
    by (simp add: lasso_rel_ext_id)
qed

text {* We define a function that chooses between the emptiness check 
  algorithms *}

datatype config_ce = CFG_CE_SCC_GABOW | CFG_CE_NDFS

definition find_ce_code where "find_ce_code cfg \<equiv> case cfg of 
  CFG_CE_SCC_GABOW \<Rightarrow> gabow_find_ce_code
| CFG_CE_NDFS \<Rightarrow> ndfs_find_ce_code"

lemma find_ce_code_refine: "is_find_ce_algo (find_ce_code cfg)"
  apply (cases cfg)
  unfolding find_ce_code_def
  using gabow_find_ce_code_refine ndfs_find_ce_code_refine
  apply (auto split: config_ce.split)
  done
  
subsection {* System-Agnostic Model-Checker *}
text {*
  In this section, we implement the part of the model-checker that does not 
  depend on the language used to describe the system to be checked. 
*}

subsubsection {* Default Implementation of Lazy Intersection *}

locale cava_inter_impl_loc =
  igba_sys_prod_precond G S
  for S :: "('s, 'l set) sa_rec"
  and G :: "('q,'l set) igba_rec" +
  fixes Gi Si Rq Rs Rl eqq
  assumes [autoref_rules]: "(eqq,op =) \<in> Rq \<rightarrow> Rq \<rightarrow> bool_rel"
  assumes [autoref_rules]: "(Gi,G) \<in> igbav_impl_rel_ext unit_rel Rq Rl"
  assumes [autoref_rules]: "(Si,S) \<in> sa_impl_rel_ext unit_rel Rs Rl"
begin

  lemma cava_inter_impl_loc_this: "cava_inter_impl_loc S G Gi Si Rq Rs Rl eqq"
    by unfold_locales

  (*<*)
  text {* TODO/FIXME:
    Some black-magic is going on here: The performance of the mc seems to depend on the ordering of states,
    so we do some adjustments of the ordering here.
  *}
  lemma prod_impl_aux_alt_cava_reorder:
    "prod = (\<lparr>
      frg_V = Collect (\<lambda>(q,s). q \<in> igba.V \<and> s \<in> sa.V),
      frg_E = E_of_succ (\<lambda>(q,s). 
        if igba.L q (sa.L s) then     
          (\<lambda>(s,q). (q,s))`(LIST_SET_REV_TAG (succ_of_E (sa.E) s) 
           \<times> (succ_of_E (igba.E) q))
        else
          {}
      ),
      frg_V0 = igba.V0 \<times> sa.V0,
      igbg_num_acc = igba.num_acc,
      igbg_acc = \<lambda>(q,s). if s\<in>sa.V then igba.acc q else {}
    \<rparr>)"
    unfolding prod_def
    apply (auto simp: succ_of_E_def E_of_succ_def split: split_if_asm)
    done

  schematic_lemma vf_prod_impl_aux_cava_reorder:
    shows "(?c, prod) \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs)"
    unfolding prod_impl_aux_alt_cava_reorder[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (trace, keep_goal))
    done

  lemma (in -) map_concat_map_map_opt: 
    "map f (concat (map (\<lambda>xa. map (f' xa) (l1 xa)) l2)) 
      = List.maps (\<lambda>xa. map (f o f' xa) (l1 xa)) l2"
    "((\<lambda>(xd, xe). (xe, xd)) \<circ> Pair xa) = (\<lambda>x. (x,xa))"
    -- "Very specific optimization used in the next refinement"
    apply -
    apply (induction l2) 
    apply (auto simp: List.maps_def) [2]

    apply auto []
    done

  concrete_definition (in -) gbav_sys_prod_impl_cava_reorder 
    for eqq Gi Si
    uses cava_inter_impl_loc.vf_prod_impl_aux_cava_reorder[
    param_fo, standard,unfolded map_concat_map_map_opt]

  lemmas [autoref_rules] = 
    gbav_sys_prod_impl_cava_reorder.refine[OF cava_inter_impl_loc_this]
  
  context begin interpretation autoref_syn .
    (* HACK: Overwrite pattern that rewrites outer-level prod, such that
      local rules apply here. *)
    lemma [autoref_op_pat]: "prod \<equiv> OP prod" by simp
  end

  (*>*)

  definition dflt_inter :: "('q \<times> 's) igb_graph_rec \<times> ('q \<times> 's \<Rightarrow> 's)" 
    where "dflt_inter \<equiv> (prod, snd)"

  lemma dflt_inter_refine: 
    shows "RETURN dflt_inter \<le> inter_spec S G"
    unfolding inter_spec_def dflt_inter_def
    apply (refine_rcg le_ASSERTI refine_vcg)
  proof clarsimp_all
    show "igb_graph prod" by (rule prod_invar)

    fix r
    show "(\<exists>r'. prod.is_acc_run r' \<and> r = snd \<circ> r') \<longleftrightarrow>
          (sa.is_run r \<and> sa.L \<circ> r \<in> igba.lang)"
      using gsp_correct1 gsp_correct2 
      apply (auto simp: comp_assoc)
      done
  qed

  schematic_lemma dflt_inter_impl_aux: 
    shows "(?c, dflt_inter) 
    \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs)"
    unfolding dflt_inter_def[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  
  concrete_definition (in -) dflt_inter_impl
    for eqq Si Gi
    uses cava_inter_impl_loc.dflt_inter_impl_aux

  lemmas [autoref_rules] = dflt_inter_impl.refine[OF cava_inter_impl_loc_this]
end

definition [simp]: "op_dflt_inter \<equiv> cava_inter_impl_loc.dflt_inter"
lemma [autoref_op_pat]: "cava_inter_impl_loc.dflt_inter \<equiv> op_dflt_inter"
  by simp


context begin interpretation autoref_syn .
lemma dflt_inter_autoref[autoref_rules]:
  fixes G :: "('q,'l set) igba_rec"
  fixes S :: "('s, 'l set) sa_rec"
  fixes Gi Si Rq Rs Rl eqq
  assumes "SIDE_PRECOND (igba G)"
  assumes "SIDE_PRECOND (sa S)"
  assumes "GEN_OP eqq op = (Rq \<rightarrow> Rq \<rightarrow> bool_rel)"
  assumes "(Gi,G) \<in> igbav_impl_rel_ext unit_rel Rq Rl"
  assumes "(Si,S) \<in> sa_impl_rel_ext unit_rel Rs Rl"
  shows "(dflt_inter_impl eqq Si Gi,
    (OP op_dflt_inter 
     ::: sa_impl_rel_ext unit_rel Rs Rl
      \<rightarrow> igbav_impl_rel_ext unit_rel Rq Rl 
      \<rightarrow> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs))$S$G
  ) \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs)"
proof -
  from assms interpret igba!: igba G by simp
  from assms interpret sa!: sa S by simp
  from assms interpret cava_inter_impl_loc S G Gi Si Rq Rs Rl eqq
    by unfold_locales simp_all

  show ?thesis
    apply simp
    apply (rule dflt_inter_impl.refine)
    apply unfold_locales
    done
qed

end

lemma inter_spec_refineI: 
  assumes "\<lbrakk> sa S; igba G \<rbrakk> \<Longrightarrow> m \<le> \<Down>R (inter_spec S G)"
  shows "m \<le> \<Down>R (inter_spec S G)"
  using assms
  unfolding inter_spec_def
  apply refine_rcg
  apply simp
  done
  
lemma dflt_inter_impl_refine: 
  fixes Rs :: "('si \<times> 's) set"
  fixes Rq :: "('qi \<times> 'q) set"
  fixes Rprop :: "('pi \<times> 'p) set"
  assumes [relator_props]: "single_valued Rs" "Range Rs = UNIV" 
    "single_valued Rq" "Range Rq = UNIV"

  assumes EQ: "(eqq,op=) \<in> Rq \<rightarrow> Rq \<rightarrow> bool_rel"

  shows "(dflt_inter_impl eqq, inter_spec)
  \<in> sa_impl_rel_ext unit_rel Rs (\<langle>Rprop\<rangle>fun_set_rel) \<rightarrow>
    igbav_impl_rel_ext unit_rel Rq (\<langle>Rprop\<rangle>fun_set_rel) \<rightarrow>
    \<langle>igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r ((Rq \<times>\<^sub>r Rs) \<rightarrow> Rs)\<rangle>plain_nres_rel"
  apply (intro fun_relI plain_nres_relI)
  apply (rule inter_spec_refineI)
proof -
  fix Si S Gi G

  assume R:"(Si,S) \<in> sa_impl_rel_ext unit_rel Rs (\<langle>Rprop\<rangle>fun_set_rel)"
    "(Gi, G) \<in> igbav_impl_rel_ext unit_rel Rq (\<langle>Rprop\<rangle>fun_set_rel)"

  assume "sa S" and "igba G"
  then interpret sa!: sa S + igba!: igba G .
  interpret cava_inter_impl_loc S G Gi Si Rq Rs "\<langle>Rprop\<rangle>fun_set_rel" eqq
    apply unfold_locales
    using EQ R by simp_all

  note RETURN_refine_sv[OF _ dflt_inter_impl.refine[OF cava_inter_impl_loc_this]]
  also note dflt_inter_refine
  finally show "RETURN (dflt_inter_impl eqq Si Gi)
  \<le> \<Down> (igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs))
     (inter_spec S G)" 
    apply rprems
    apply tagged_solver
    done
qed

subsubsection {* Definition of Model-Checker *}
text {* In this section, we instantiate the parametrized model checker
  with the actual implementations. *}

setup Locale_Code.open_block
interpretation cava_sys_agn!: impl_model_checker 
  "sa_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)" 
  "igbav_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)"
  "igbg_impl_rel_ext unit_rel (Id \<times>\<^sub>r Id)"
  "\<langle>Id \<times>\<^sub>r Id\<rangle>lasso_run_rel" "\<langle>Id\<rangle>lasso_run_rel"

  "ltl_to_gba_code"
  "\<lambda>_::unit. dflt_inter_impl op ="
  "find_ce_code"
  "map_lasso"
  apply unfold_locales
  apply tagged_solver

  apply (rule ltl_to_gba_code_refine[unfolded is_ltl_to_gba_algo_def])
  
  using dflt_inter_impl_refine[of Id Id "op =" Id] apply simp

  using find_ce_code_refine[unfolded is_find_ce_algo_def] 
  apply simp apply assumption

  using map_lasso_run_refine[of Id Id] apply simp
  done
setup Locale_Code.close_block

definition "cava_sys_agn \<equiv> cava_sys_agn.impl_model_check"

text {* The correctness theorem states correctness of the model checker wrt.\ 
  a model given as system automata. In the following sections, we will then 
  refine the model description to Boolean programs and Promela. *}
theorem cava_sys_agn_correct:
  fixes sysi :: "('s::hashable, 'p::linorder \<Rightarrow> bool, unit) sa_impl_scheme" 
    and sys :: "('s, 'p set) sa_rec" 
    and \<phi> :: "'p ltlc" 
    and cfg :: "config_l2b \<times> unit \<times> config_ce" 
  assumes "(sysi, sys) \<in> sa_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)"
    and "sa sys"
  shows "case cava_sys_agn cfg sysi \<phi> of
         None \<Rightarrow> sa.lang sys \<subseteq> ltlc_language \<phi> 
         | Some None \<Rightarrow> \<not> sa.lang sys \<subseteq> ltlc_language \<phi>
         | Some (Some L) \<Rightarrow> 
             fr_graph.is_run sys (run_of_lasso L) 
           \<and> sa_L sys \<circ> (run_of_lasso L) \<notin> ltlc_language \<phi>"
  using cava_sys_agn.impl_model_check_correct[OF assms, of \<phi> cfg]
  unfolding cava_sys_agn_def
  by (auto split: option.splits simp: lasso_run_rel_def br_def)


subsection {* Model Checker for Boolean Programs *}

definition bpc_to_sa 
  :: "bprog \<times> BoolProgs.config \<Rightarrow> (BoolProgs.config,nat set) sa_rec" 
  -- "Conversion of a Boolean program to a system automata."
  where 
  "bpc_to_sa bpc \<equiv> let (bp,c0)=bpc in
  \<lparr>
    frg_V = UNIV,
    frg_E = E_of_succ (set o BoolProgs.nexts bp),
    frg_V0 = {c0},
    sa_L = \<lambda>c. bs_\<alpha> (snd c)
  \<rparr>"

definition bpc_to_sa_impl 
  :: "bprog \<times> BoolProgs.config 
  \<Rightarrow> (BoolProgs.config,nat \<Rightarrow> bool,unit) sa_impl_scheme" 
  where 
  "bpc_to_sa_impl bpc \<equiv> let (bp,c0)=bpc in
  \<lparr> frgi_V = \<lambda>_. True,
    frgi_E = remdups o BoolProgs.nexts bp,
    frgi_V0 = [c0],
    sai_L = \<lambda>c i. bs_mem i (snd c)
  \<rparr>"

lemma bpc_to_sa_impl_refine: "(bpc_to_sa_impl bpc, bpc_to_sa bpc) 
  \<in> sa_impl_rel_ext unit_rel Id (\<langle>nat_rel\<rangle>fun_set_rel)"
  unfolding bpc_to_sa_impl_def bpc_to_sa_def 
  unfolding sa_impl_rel_eext_def frg_impl_rel_ext_def
  unfolding gen_sa_impl_rel_eext_def gen_frg_impl_rel_ext_def
  apply (clarsimp split: prod.split)
  apply (intro conjI)
  apply (auto simp: fun_set_rel_def br_def) []

  apply (rule E_of_succ_refine[param_fo])
  apply (auto simp: list_set_rel_def br_def) []

  apply (auto simp: list_set_rel_def br_def) []

  apply (auto simp: fun_set_rel_def br_def) []
  done


lemma bpc_to_sa_invar: "sa (bpc_to_sa bpc)"
proof -
  obtain bp c where [simp]: "bpc = (bp,c)" by (cases bpc)
  show ?thesis
    apply unfold_locales

    apply (simp add: bpc_to_sa_def)
    thm BoolProgs.reachable_configs_finite

    apply (rule finite_subset[OF _ BoolProgs.reachable_configs_finite[of bp c]])
    apply (rule rtrancl_reachable_induct)
    apply (auto 
      intro: BoolProgs.reachable_configs.intros 
      simp: E_of_succ_def) [2]

    apply (simp add: bpc_to_sa_def)
    apply (simp add: bpc_to_sa_def)
    done
qed

interpretation bpc_to_sa!: sa "(bpc_to_sa bpc)"
  using bpc_to_sa_invar .

lemma bpc_to_sa_run_conv[simp]: 
  "fr_graph.is_run (bpc_to_sa bpc) = bpc_is_run bpc"
  apply (rule ext)
  unfolding bpc_to_sa.is_run_def
  unfolding bpc_to_sa_def bpc_is_run_def 
    ipath_def E_of_succ_def
  by auto

lemma bpc_to_sa_L_conv[simp]: "sa_L (bpc_to_sa bpc) = bpc_props"
  apply (rule ext)
  unfolding bpc_to_sa_def bpc_props_def
  apply (auto simp: E_of_succ_def split: prod.split)
  done

lemma bpc_to_sa_lang_conv[simp]: "sa.lang (bpc_to_sa bpc) = bpc_lang bpc"
  unfolding bpc_to_sa.lang_def bpc_to_sa.accept_def[abs_def] bpc_lang_def
  by auto

definition "cava_bpc cfg bpc \<phi> \<equiv> cava_sys_agn cfg (bpc_to_sa_impl bpc) \<phi>"

text {*
  Correctness theorem for the model checker on boolean programs.
  Note that the semantics of Boolean programs is given 
  by @{const "bpc_lang"}.
*}
theorem cava_bpc_correct:
  "case cava_bpc cfg bpc \<phi> of 
    None \<Rightarrow> bpc_lang bpc \<subseteq> ltlc_language \<phi>
  | Some None \<Rightarrow> (\<not>(bpc_lang bpc \<subseteq> ltlc_language \<phi>))
  | Some (Some ce) \<Rightarrow> 
      bpc_is_run bpc (run_of_lasso ce) 
    \<and> bpc_props o run_of_lasso ce \<notin> ltlc_language \<phi>"
  using cava_sys_agn_correct[OF bpc_to_sa_impl_refine bpc_to_sa_invar, 
    of bpc \<phi> cfg]
  unfolding cava_bpc_def
  by (auto split: option.split simp: lasso_run_rel_def br_def)

export_code cava_bpc checking SML

subsection {* Model Checker for Promela Programs *}

definition promela_to_sa 
  :: "promela \<times> PromelaLTL.config \<Rightarrow> (PromelaLTL.config, nat set) sa_rec" 
  -- "Conversion of a Promela model to a system automata."
  where "promela_to_sa promc \<equiv> let (prom,c\<^sub>0)=promc in
  \<lparr>
    frg_V = UNIV,
    frg_E = E_of_succ (ls.\<alpha> o PromelaLTL.nexts_code prom),
    frg_V0 = {c\<^sub>0},
    sa_L = bs_\<alpha> \<circ> fst
  \<rparr>"

definition promela_to_sa_impl 
  :: "promela \<times> PromelaLTL.config 
  \<Rightarrow> (PromelaLTL.config, nat \<Rightarrow> bool, unit) sa_impl_scheme" where 
  "promela_to_sa_impl promc \<equiv> let (prom,c\<^sub>0)=promc in
  \<lparr> frgi_V = \<lambda>_. True,
    frgi_E = ls.to_list o PromelaLTL.nexts_code prom,
    frgi_V0 = [c\<^sub>0],
    sai_L = \<lambda>c i. bs_mem i (fst c)
  \<rparr>"

lemma promela_to_sa_impl_refine: 
  "(promela_to_sa_impl promc, promela_to_sa promc) 
  \<in> sa_impl_rel_ext unit_rel Id (\<langle>nat_rel\<rangle>fun_set_rel)"
  unfolding promela_to_sa_impl_def promela_to_sa_def 
  unfolding sa_impl_rel_eext_def frg_impl_rel_ext_def
  unfolding gen_sa_impl_rel_eext_def gen_frg_impl_rel_ext_def

  apply (clarsimp split: prod.split)
  apply (intro conjI)

  apply (auto simp: fun_set_rel_def br_def) []

  apply (rule E_of_succ_refine[param_fo])
  apply (auto simp: list_set_rel_def br_def ls.correct) []

  apply (auto simp: list_set_rel_def br_def) []
  apply (auto simp: fun_set_rel_def br_def in_set_member) []
  done


definition "cava_promela cfg promc \<phi> \<equiv> cava_sys_agn cfg (promela_to_sa_impl promc) \<phi>"

lemma cava_promela_correct_aux:
  assumes "promela_inv prom" and "config_inv prom c\<^sub>0"
  shows 
  "case cava_promela cfg (prom,c\<^sub>0) \<phi> of 
    None \<Rightarrow> promela_language (prom,c\<^sub>0) \<subseteq> ltlc_language \<phi>
  | Some None \<Rightarrow> (\<not>(promela_language (prom,c\<^sub>0) \<subseteq> ltlc_language \<phi>))
  | Some (Some ce) \<Rightarrow> promela_is_run (prom,c\<^sub>0) (run_of_lasso ce) 
    \<and> promela_props o run_of_lasso ce \<notin> ltlc_language \<phi>"
proof -
  have promela_to_sa_invar: "sa (promela_to_sa (prom,c\<^sub>0))"
  proof -
    show ?thesis
      apply unfold_locales
      apply (simp add: promela_to_sa_def)
      apply (rule 
        finite_subset[OF _ PromelaLTL.reachable_configs_finite[of prom c\<^sub>0]])
      apply (rule rtrancl_reachable_induct)
      apply (auto 
        intro: PromelaLTL.reachable_configs.intros 
        simp: E_of_succ_def) [2]
      apply fact
      apply fact
      
      apply (simp add: promela_to_sa_def)
      apply (simp add: promela_to_sa_def)
      done
  qed

  interpret promela_to_sa!: sa "promela_to_sa (prom,c\<^sub>0)"
    using promela_to_sa_invar .

  have promela_to_sa_run_conv[simp]: 
    "fr_graph.is_run (promela_to_sa (prom,c\<^sub>0)) = promela_is_run (prom,c\<^sub>0)"
    apply (rule ext)
    unfolding promela_to_sa.is_run_def
    unfolding promela_to_sa_def promela_is_run_def ipath_def E_of_succ_def
    by auto

  have promela_to_sa_L_conv[simp]: 
    "sa_L (promela_to_sa (prom,c\<^sub>0)) = promela_props"
    apply (rule ext)
    unfolding promela_to_sa_def promela_props_def
    by (auto simp: E_of_succ_def split: prod.split)

  have promela_to_sa_lang_conv[simp]: 
    "sa.lang (promela_to_sa (prom,c\<^sub>0)) = promela_language (prom,c\<^sub>0)"
    unfolding promela_to_sa.lang_def promela_to_sa.accept_def[abs_def]
      promela_language_def
    by auto
  
  show ?thesis
    using cava_sys_agn_correct[OF 
      promela_to_sa_impl_refine promela_to_sa_invar, of \<phi> cfg]
    unfolding cava_promela_def
    by (auto split: option.split simp: lasso_run_rel_def br_def)
qed

text {*
  The next theorem states correctness of the Promela model checker. 

  Note that the function @{const "PromelaLTL.prepare"} processes the
  promela model and the formula into a system automaton and a 
  new formula over different APs. 
  The correctness theorem is specified in terms of the system automata and 
  the processed formula.
*}
theorem cava_promela_correct:
  assumes "PromelaLTL.prepare ltlChoose ast = (promc, \<phi>)"
  shows 
  "case cava_promela cfg promc \<phi> of 
    None \<Rightarrow> promela_language promc \<subseteq> ltlc_language \<phi>
  | Some None \<Rightarrow> (\<not>(promela_language promc \<subseteq> ltlc_language \<phi>))
  | Some (Some ce) \<Rightarrow> 
      promela_is_run promc (run_of_lasso ce) 
    \<and> promela_props o run_of_lasso ce \<notin> ltlc_language \<phi>"
proof -
  obtain prom c where promcFmt[simp]: "promc = (prom,c)" by (cases promc)
  
  show ?thesis
    apply (subst promcFmt)+
    apply (rule cava_promela_correct_aux)
    using prepare_connect[of ltlChoose ast prom c \<phi>] assms by simp_all
qed

export_code cava_promela checking SML

subsection {* Extraction of SML Code *}

definition "dflt_cfg \<equiv> (CFG_L2B_GERTHS,(),CFG_CE_SCC_GABOW)"

code_identifier 
  code_module CAVA_Impl_New \<rightharpoonup> (SML) CAVA and (Haskell) CAVA

export_code cava_bpc cava_promela dflt_cfg
            BoolProgs.print_config ltl_conv chose_prog list_progs (*BP specials*)
            printProcesses PromelaLTL.prepare PromelaLTL.printConfig (*Promela specials*)
            frv_export_code
            lasso_v0 lasso_va lasso_reach lasso_cycle
            nat_of_integer int_of_integer
            integer_of_nat integer_of_int
  checking SML 

export_code cava_bpc cava_promela dflt_cfg
            BoolProgs.print_config ltl_conv chose_prog list_progs (*BP specials*)
            printProcesses PromelaLTL.prepare PromelaLTL.printConfig (*Promela specials*)
            frv_export_code
            lasso_v0 lasso_va lasso_reach lasso_cycle
            nat_of_integer int_of_integer
            integer_of_nat integer_of_int
  in SML 
  file "code/CAVA_Export.sml"

end
