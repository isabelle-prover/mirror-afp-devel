header {* \isaheader{Automatic Data Refinement} *}
theory Refine_Autoref 
imports 
  Refine_Basic 
  Refine_While 
  Refine_Foreach 
  Refine_Heuristics 
  (*"../Collections/Collections"*)
begin
  text {*
    This theory demonstrates a possible approach to automatic data refinement 
    according to some type-based and tag-based rules.

    Note that this is still a prototype.
    *}

subsection {* Preliminaries *}
  text {* Preliminaries for idtrans-tac, that transfers operations along 
    identity relation. *}
  lemma idtrans0: "(f,f)\<in>Id" by simp
  lemma idtrans_arg: "(f,f')\<in>Id \<Longrightarrow> (a,a')\<in>Id \<Longrightarrow> (f a,f' a')\<in>Id" by simp

subsection {* Setup *}
ML {*
structure Refine_Autoref = struct
  open Refine_Misc;
  (******************************)
  (* Theorem Collections *)
  (******************************)

  structure prg_thms = Named_Thms
    ( val name = @{binding autoref_prg}
      val description = "Automatic Refinement: Program translation rules." );

  structure exp_thms = Named_Thms
    ( val name = @{binding autoref_ex}
      val description = "Automatic Refinement: Expression translation rules.");

  structure spec_thms = Named_Thms
    ( val name = @{binding autoref_spec}
      val description = "Automatic Refinement: Specification rules"
        ^"decomposition rules." );

  structure other_thms = Named_Thms
    ( val name = @{binding autoref_other}
      val description = "Automatic Refinement: Rules for subgoals of "
      ^"other types" );

  structure elim_thms = Named_Thms
    ( val name = @{binding autoref_elim}
      val description = "Automatic Refinement: Preprocessing elim rules" );

  structure simp_thms = Named_Thms
    ( val name = @{binding autoref_simp}
      val description = "Automatic Refinement: Preprocessing simp rules" );

  type config = {
    prg_thms : thm list,
    exp_thms : thm list,
    spec_thms : thm list,
    other_thms : thm list,
    elim_thms : thm list,
    simp_ss : simpset,
    trace : bool
  };


  (******************************)
  (* Tactics *)
  (******************************)

  (*
    The following function classifies the current subgoal into one of
    the following categories. It is used by the main tactic to decide how
    to proceed.
  *)
  datatype ref_goal =                  (* Argument order is always (C,R,A) *)
    Rg_prg_ref of term * term * term  | (* C \<le>\<Down>R A *)
    Rg_var_ref of term * term * term  | (* (C,A)\<in>R where A is var/free *)
    Rg_spec_ref of term * term * term | (* (C,A)\<in>?R, where type C has var *)
    Rg_exp_ref of term * term * term  | (* (C,A)\<in>R [where hd R is constant] *)
    Rg_other   of term                | (* Any other conlcusion *)
    Rg_invalid of term;                 (* Invalid *)

  fun dest_refinement_goal ctxt i st = let
    (* Test to detect schematic variables on wrong side *)
    fun test_var t res = if exists_subterm is_Var t then 
      Rg_invalid t else res;
  in
    if i <= nprems_of st then case
      Logic.concl_of_goal (prop_of st) i |> HOLogic.dest_Trueprop 
      |> Envir.beta_eta_contract
    of
      (Const (@{const_name "Orderings.ord_class.less_eq"}, _) $
        c $ (Const (@{const_name "Refine_Basic.conc_fun"},_) $ r $ a)) =>
        test_var a (Rg_prg_ref (c,r,a))
    | (Const (@{const_name "Set.member"},_) $ 
        (Const(@{const_name "Product_Type.Pair"},_)$c$a)$r) =>
      if is_Free a orelse is_Var a then test_var a (Rg_var_ref (c,r,a))
      else if exists_subtype is_TVar (fastype_of c) then 
        test_var a (Rg_spec_ref (c,r,a))
      else test_var a (Rg_exp_ref (c,r,a))
    | t => Rg_other t
    else (Rg_invalid (prop_of st))
  end;

  (* Check whether term is a goal suited for idtrans. In positive case,
    return head function and number of arguments. 
    Check whether goal has the form: (_,t)\<in>_ where t=f a1 \<dots>an,
    and return f and n.
  *)
  fun dest_idtrans_aexp (_,r,a) = (
    case strip_comb a of
      (c as (Const _),args) => SOME (c,length args)
    | (f as (Free _),args) => SOME (f,length args)
    | _  => NONE);

  fun idtrans_tac ctxt a i st = case dest_idtrans_aexp a of
    SOME (f,argn) => let
      val certify = cterm_of (Proof_Context.theory_of ctxt);
      val idtrans0_thm = @{thm idtrans0};
      val f_var = idtrans0_thm |> concl_of |> HOLogic.dest_Trueprop 
        |> strip_comb |> snd |> hd |> strip_comb |> snd |> hd;

      val inst = [(certify f_var,certify f)];

      fun do_inst 0 = Drule.cterm_instantiate inst idtrans0_thm
      | do_inst n = do_inst (n-1) RS @{thm idtrans_arg};

      val thm = do_inst argn;
    in rtac thm i st end
  | _ => no_tac st; 
  
  fun preprocess_tac ctxt (cfg:config) =
    ((Method.assm_tac ctxt ORELSE' full_simp_tac (#simp_ss cfg)) 
       THEN_ALL_NEW (TRY o REPEAT_ALL_NEW 
         (Tactic.eresolve_tac (#elim_thms cfg)))
       );

  fun trace_rg ctxt rg = let
    fun ts_term t = Pretty.string_of (Syntax.pretty_term ctxt t);
    fun ts_triple (c,r,a) = "("^ts_term c^" | "^ts_term r^" | "^ts_term a^")"
  in tracing (
    case rg of 
      Rg_prg_ref t => "prg_ref: "^ts_triple t
    | Rg_exp_ref t => "exp_ref: "^ts_triple t
    | Rg_var_ref t => "var_ref: "^ts_triple t
    | Rg_spec_ref t => "spec_ref: "^ts_triple t
    | Rg_other t => "other: "^ts_term t
    | Rg_invalid t => "invalid: "^ts_term t
  ) end

  fun trace_sg ctxt i st = ();
    (*if i <= nprems_of st then tracing (PolyML.makestring (cprem_of st i))
    else ();*)
      
  fun autoref_tac (cfg:config) sstep ctxt i st = let
    val recurse_tac = if sstep then K all_tac else autoref_tac cfg sstep ctxt;
    val rg = dest_refinement_goal ctxt i st;
    val _ = if #trace cfg then 
      (trace_rg ctxt rg; trace_sg ctxt i st) 
      else ();
    
  in
    case rg of 
      Rg_prg_ref _ => ( 
        preprocess_tac ctxt cfg THEN_ALL_NEW 
          ( resolve_tac (#prg_thms cfg) 
            ORELSE' ( resolve_tac (#exp_thms cfg) THEN_ALL_NEW_FWD recurse_tac)
            ORELSE' rprems_tac ctxt (* Match with induction premises from REC *)
          )    
      ) i st
    | Rg_var_ref (c,r,a) => ( 
      preprocess_tac ctxt cfg THEN_ALL_NEW atac)  i st
    | Rg_spec_ref (c,r,a) => 
      (preprocess_tac ctxt cfg THEN_ALL_NEW
        (resolve_tac (#spec_thms cfg) THEN_ALL_NEW_FWD recurse_tac)
      ) i st
    | Rg_exp_ref (c,r,a) => (preprocess_tac ctxt cfg THEN_ALL_NEW
      FIRST' [resolve_tac (#exp_thms cfg), idtrans_tac ctxt (c,r,a)]
        THEN_ALL_NEW_FWD recurse_tac 
      ) i st
    | Rg_other _ => ((
        triggered_mono_tac ctxt ORELSE'  
        REPEAT_ALL_NEW (CHANGED_PROP o ares_tac (#other_thms cfg))) i st)
    | Rg_invalid _ => (no_tac st)
  end;
  
  fun dflt_config ctxt add_spec_thms trace = {
    prg_thms = prg_thms.get ctxt,
    exp_thms = exp_thms.get ctxt,
    spec_thms = add_spec_thms @ spec_thms.get ctxt,
    other_thms = other_thms.get ctxt,
    elim_thms = elim_thms.get ctxt,
    simp_ss = HOL_basic_ss addsimps (simp_thms.get ctxt),
    trace=trace
  };

  fun autoref_method trace ss as_thms ctxt = let
    val cfg = dflt_config ctxt as_thms trace
  in 
    if ss then
      SIMPLE_METHOD' (
        CHANGED_PROP o (autoref_tac cfg true ctxt))
    else
      SIMPLE_METHOD' (
        CHANGED_PROP o REPEAT_DETERM' (CHANGED_PROP o
          autoref_tac cfg false ctxt))
  end

end *}

setup {* Refine_Autoref.prg_thms.setup *}
setup {* Refine_Autoref.exp_thms.setup *}
setup {* Refine_Autoref.spec_thms.setup *}
setup {* Refine_Autoref.other_thms.setup *}
setup {* Refine_Autoref.elim_thms.setup *}
setup {* Refine_Autoref.simp_thms.setup *}

method_setup refine_autoref =
  {* (Args.mode "trace" -- Args.mode "ss" -- Attrib.thms) 
    >> (fn ((trace,ss),as_thms) => fn ctxt 
         => Refine_Autoref.autoref_method trace ss as_thms ctxt) *} 
  "Refinement Framework: Automatic data refinement"


(*
method_setup refine_autoref =
  {* (Args.mode "trace" -- Args.mode "ss" -- Attrib.thms) 
    >> (fn ((trace,ss),as_thms) => fn ctxt => SIMPLE_METHOD' (
    CHANGED_PROP o Refine_Autoref.REPEAT_DETERM' (CHANGED_PROP o
      Refine_Autoref.autoref_tac (Refine_Autoref.dflt_config ctxt as_thms 
          trace) 
        ss ctxt))
  ) *} 
  "Refinement Framework: Automatic data refinement"
*)
(*method_setup refine_autoref_ss =
  {* (Args.mode "notrace" -- Attrib.thms) 
    >> (fn (notrace,as_thms) => fn ctxt => SIMPLE_METHOD' (
    CHANGED_PROP o (Refine_Autoref.autoref_tac 
        (Refine_Autoref.dflt_config ctxt as_thms (not notrace)) true ctxt))
  ) *} 
  "Refinement Framework: Automatic data refinement (single step mode)"
*)

subsection {* Configuration *}
text {*
  We now add the default configuration for the automatic refinement tactic,
  including decomposition statements for most program constructs, and
  some default setup for product types in expressions.
*}

subsubsection {* Program Constructs *}
  lemma Let_autoref[autoref_prg]:
    assumes "(x,x')\<in>R'"
    assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le>\<Down>R (f' x')"
    shows "Let x f \<le>\<Down>R (Let x' f')"
    using assms
    by (auto simp: pw_le_iff refine_pw_simps)

  lemmas std_constructs_autoref_aux = 
    bind_refine ASSERT_refine_right if_refine
    WHILET_refine WHILE_refine WHILET_refine' WHILE_refine'

  lemmas [autoref_prg] = std_constructs_autoref_aux[folded pair_in_Id_conv]

  lemma REC_autoref[autoref_prg]:
    assumes R0: "(x,x')\<in>R"
    assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
      \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
    assumes M: "mono body"
    shows "REC body x \<le>\<Down>S (REC body' x')"
    by (rule REC_refine[OF M R0 RS]) 

  lemma RECT_autoref[autoref_prg]:
    assumes R0: "(x,x')\<in>R"
    assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
      \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
    assumes M: "mono body"
    shows "RECT body x \<le>\<Down>S (RECT body' x')"
    by (rule RECT_refine[OF M R0 RS]) 

  lemma RETURN_autoref[autoref_prg]:
    "\<lbrakk>(x, x') \<in> R; single_valued R\<rbrakk> \<Longrightarrow> RETURN x \<le> \<Down> R (RETURN x')"
    using RETURN_refine_sv .

  lemma FOREACH_autoref[autoref_prg]:
    fixes S :: "'S set"
    assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
    assumes REFS: "(S,S')\<in>Id"
    assumes SV: "single_valued R"
    assumes REFSTEP: "\<And>\<sigma> \<sigma>' x x'. \<lbrakk> (\<sigma>,\<sigma>')\<in>R; (x,x')\<in>Id \<rbrakk> \<Longrightarrow> f x \<sigma> 
      \<le> \<Down>R (f' x' \<sigma>')"
    shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACH S' f' \<sigma>0')"
    apply (rule FOREACH_refine[OF inj_on_id, where \<Phi>''="\<lambda>_ _ _ _. True"])
    using assms by auto

  lemma FOREACHi_autoref[autoref_prg]:
    fixes S :: "'S set"
    assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
    assumes REFS: "(S,S')\<in>Id"
    assumes SV: "single_valued R"
    assumes REFSTEP: "\<And>\<sigma> \<sigma>' x x'. \<lbrakk> (\<sigma>,\<sigma>')\<in>R; (x,x')\<in>Id \<rbrakk> \<Longrightarrow> f x \<sigma> 
      \<le> \<Down>R (f' x' \<sigma>')"
    shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACHi I S' f' \<sigma>0')"
    unfolding FOREACH_def FOREACHc_def FOREACHi_def
    apply (rule FOREACHci_refine[OF inj_on_id, where \<Phi>''="\<lambda>_ _ _ _. True"])
    using assms by auto

  lemma FOREACHc_autoref[autoref_prg]:
    fixes S :: "'S set"
    assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
    assumes REFS: "(S,S')\<in>Id"
    assumes SV: "single_valued R"
    assumes REFC: "\<And>\<sigma> \<sigma>'. (\<sigma>,\<sigma>')\<in>R \<Longrightarrow> (c \<sigma>, c' \<sigma>')\<in>Id"
    assumes REFSTEP: "\<And>\<sigma> \<sigma>' x x'. \<lbrakk> (\<sigma>,\<sigma>')\<in>R; (x,x')\<in>Id \<rbrakk> \<Longrightarrow> f x \<sigma> 
      \<le> \<Down>R (f' x' \<sigma>')"
    shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHc S' c' f' \<sigma>0')"
    apply (rule FOREACHc_refine[OF inj_on_id, where \<Phi>''="\<lambda>_ _ _ _. True"])
    using assms by auto

  lemma FOREACHci_autoref[autoref_prg]:
    fixes S :: "'S set"
    assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
    assumes REFS: "(S,S')\<in>Id"
    assumes SV: "single_valued R"
    assumes REFC: "\<And>\<sigma> \<sigma>'. (\<sigma>,\<sigma>')\<in>R \<Longrightarrow> (c \<sigma>, c' \<sigma>')\<in>Id"
    assumes REFSTEP: "\<And>\<sigma> \<sigma>' x x'. \<lbrakk> (\<sigma>,\<sigma>')\<in>R; (x,x')\<in>Id \<rbrakk> \<Longrightarrow> f x \<sigma> 
      \<le> \<Down>R (f' x' \<sigma>')"
    shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHci I S' c' f' \<sigma>0')"
    unfolding FOREACH_def FOREACHc_def FOREACHi_def
    apply (rule FOREACHci_refine[OF inj_on_id, where \<Phi>''="\<lambda>_ _ _ _. True"])
    using assms by auto

subsubsection {* Product splitting *}
  text {*
    Product splitting has not yet been solved properly. Below, you see the
    current hack that works in many cases.
    *}
  lemma rprod_iff[autoref_simp]: 
    "((a,b),(a',b'))\<in>rprod R1 R2 \<longleftrightarrow> (a,a')\<in>R1 \<and> (b,b')\<in>R2" by auto
  (*lemmas [autoref_simp] = split_paired_all*)
  lemmas [autoref_elim] = conjE impE

  lemma prod_id_split[autoref_simp]: "Id = rprod Id Id" by auto

  declare nested_prod_case_simp[autoref_simp]

  lemma prod_split_elim[autoref_elim]: 
    "\<lbrakk>(x,x')\<in>rprod Ra Rb; 
      \<And>a b a' b'. \<lbrakk>x=(a,b); x'=(a',b'); (a,a')\<in>Ra; (b,b')\<in>Rb\<rbrakk> 
        \<Longrightarrow> (f a b,f' (a',b'))\<in>R 
    \<rbrakk> 
    \<Longrightarrow> (prod_case f x,f' x')\<in>R" by auto

  lemma prod_split_elim_prg[autoref_elim]: 
    "\<lbrakk>(x,x')\<in>rprod Ra Rb; 
      \<And>a b a' b'. \<lbrakk>x=(a,b); x'=(a',b'); (a,a')\<in>Ra; (b,b')\<in>Rb\<rbrakk> 
        \<Longrightarrow> f a b \<le> \<Down>R (f' (a',b')) 
    \<rbrakk> 
    \<Longrightarrow> prod_case f x \<le>\<Down>R (f' x')" by auto

  lemma rprod_spec: 
    fixes ca :: 'ca and cb::'cb and aa::'aa and ab::'ab
    assumes "(ca,aa)\<in>Ra" 
    assumes "(cb,ab)\<in>Rb" 
    shows "((ca,cb),(aa,ab))\<in>rprod Ra Rb"
    using assms by auto

  text {* This will split all products by default. In most cases, this is
    the desired behaviour, otherwise the lemma should be removed in your local
    theory by @{text "declare rprod_spec[autoref_spec del]"}
    *}
  declare rprod_spec[autoref_spec]

  lemma prod_case_autoref_ex[autoref_ex]:
    assumes "(f, f' a' b')\<in>R"
    shows "(f, prod_case f' (a',b'))\<in>R"
    using assms by auto

  lemma prod_case_autoref_prg[autoref_prg]:
    assumes "f \<le>\<Down>R (f' a' b')"
    shows "f \<le>\<Down>R (prod_case f' (a',b'))"
    using assms by auto

  lemma pair_autoref[autoref_ex]:
    "\<lbrakk> (a,a')\<in>Ra; (b,b')\<in>Rb \<rbrakk> \<Longrightarrow> ((a,b),(a',b'))\<in>rprod Ra Rb"
    by auto

subsubsection {* Discharging single-valued goals *}
  lemmas [autoref_other] = br_single_valued rprod_sv single_valued_Id
    map_list_rel_sv map_set_rel_sv

subsubsection {* Tagging *}
  text {*
    Tags can be used to stop the processing at the tagged term, or
    to apply some special rules to the tagged translation.
    *}

  text {* Named tag to be placed around a term *}
  definition TAG :: "string \<Rightarrow> 'a \<Rightarrow> 'a" where [simp]: "TAG s = id"

  text {* To be used as @{text "simp only: TAG_remove"} or 
    @{text "unfold TAG_remove"}, to safely remove tags from
    program. *}
  lemma TAG_remove[simp]: "TAG s t = t" by simp

  text {* Remove tag. To be used partially instantiated as spec-rule *}
  lemma TAG_dest:
    assumes "(c::'c,a::'a)\<in>R"
    shows "(c,TAG name a)\<in>R"
    using assms by auto

  text {* Specify refinement relation. To be used partially instantiated as
    spec-rule.*}
  lemma spec_R: 
    fixes c::"'c" and a::"'a"
    assumes "(c,a)\<in>R"
    shows "(c,a)\<in>R"
    by fact

  text {* Specify identity translation. To be used partially instantiated as
    spec-rule. *}
  lemma spec_Id:
    fixes c::"'a" and a::"'a"
    assumes "(c,a)\<in>Id"
    shows "(c,a)\<in>Id"
    by fact

subsection {* Convenience Lemmas *}

text {* Introduce autoref, determinize, optimize *}
lemma autoref_det_optI:
  assumes "m \<le> \<Down>R a"
  assumes "\<alpha> c' \<le> m"
  assumes "c = c'"
  shows "\<alpha> c \<le> \<Down>R a"
  using assms by auto

text {* Introduce autoref, determinize *}
lemma autoref_detI:
  assumes "m \<le> \<Down>R a"
  assumes "\<alpha> c \<le> m"
  shows "\<alpha> c \<le> \<Down>R a"
  using assms by auto

text {* To be used in optimize phase: *}
lemma prod_case_rename:
  "prod_case (\<lambda>a _. f a) = f o fst"
  "prod_case (\<lambda>_ b. f b) = f o snd"
  by (auto)

end
