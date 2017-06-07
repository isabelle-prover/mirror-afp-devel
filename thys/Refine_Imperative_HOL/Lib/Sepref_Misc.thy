theory Sepref_Misc
imports 
  "../../Refine_Monadic/Refine_Monadic"
  PO_Normalizer
  "../../List-Index/List_Index"
  "../../Separation_Logic_Imperative_HOL/Sep_Main"
  Named_Theorems_Rev
  "~~/src/HOL/Eisbach/Eisbach"
  "../../Separation_Logic_Imperative_HOL/Examples/Array_Blit"
begin

  hide_const (open) CONSTRAINT

  (* Additions for List_Index *)  
  lemma index_of_last_distinct[simp]: 
    "distinct l \<Longrightarrow> index l (last l) = length l - 1"  
    apply (cases l rule: rev_cases)
    apply (auto simp: index_append)
    done

  lemma index_eqlen_conv[simp]: "index l x = length l \<longleftrightarrow> x\<notin>set l"
    by (auto simp: index_size_conv)

  (* TODO: Move *)
  text \<open>Lexicographic measure, assuming upper bound for second component\<close>
  lemma mlex_fst_decrI:
    fixes a a' b b' N :: nat
    assumes "a<a'"
    assumes "b<N" "b'<N"
    shows "a*N + b < a'*N + b'"
  proof -  
    have "a*N + b + 1 \<le> a*N + N" using \<open>b<N\<close> by linarith 
    also have "\<dots> \<le> a'*N" using \<open>a<a'\<close>
      by (metis Suc_leI ab_semigroup_add_class.add.commute 
        ab_semigroup_mult_class.mult.commute mult_Suc_right mult_le_mono2) 
    also have "\<dots> \<le> a'*N + b'" by auto
    finally show ?thesis by auto
  qed      
    
  lemma mlex_leI:
    fixes a a' b b' N :: nat
    assumes "a\<le>a'"
    assumes "b\<le>b'"
    shows "a*N + b \<le> a'*N + b'"
    using assms
    by (auto intro!: add_mono)
      
  lemma mlex_snd_decrI:
    fixes a a' b b' N :: nat
    assumes "a=a'"
    assumes "b<b'"
    shows "a*N + b < a'*N + b'"
    using assms
    by (auto)

  lemma mlex_bound:  
    fixes a b :: nat
    assumes "a<A"
    assumes "b<N"
    shows "a*N + b < A*N"
    using assms
    using mlex_fst_decrI by fastforce



  text \<open>Uncurry0\<close>  
  definition "uncurry0 c \<equiv> \<lambda>_::unit. c"
  definition curry0 :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a" where "curry0 f = f ()"
  lemma uncurry0_apply[simp]: "uncurry0 c x = c" by (simp add: uncurry0_def)

  lemma curry_uncurry0_id[simp]: "curry0 (uncurry0 f) = f" by (simp add: curry0_def)
  lemma uncurry_curry0_id[simp]: "uncurry0 (curry0 g) = g" by (auto simp: curry0_def)
  lemma param_uncurry0[param]: "(uncurry0,uncurry0) \<in> A \<rightarrow> (unit_rel\<rightarrow>A)" by auto
    
  text \<open>Abbreviations for higher-order uncurries\<close>    
  abbreviation "uncurry2 f \<equiv> uncurry (uncurry f)"
  abbreviation "curry2 f \<equiv> curry (curry f)"
  abbreviation "uncurry3 f \<equiv> uncurry (uncurry2 f)"
  abbreviation "curry3 f \<equiv> curry (curry2 f)"
  abbreviation "uncurry4 f \<equiv> uncurry (uncurry3 f)"
  abbreviation "curry4 f \<equiv> curry (curry3 f)"
  abbreviation "uncurry5 f \<equiv> uncurry (uncurry4 f)"
  abbreviation "curry5 f \<equiv> curry (curry4 f)"

  lemma fold_partial_uncurry: "uncurry (\<lambda>(ps, cf). f ps cf) = uncurry2 f" by auto

  lemma curry_shl: 
    "\<And>g f. (g \<equiv> curry f) \<equiv> (uncurry g \<equiv> f)"
    "\<And>g f. (g \<equiv> curry0 f) \<equiv> (uncurry0 g \<equiv> f)"
    by (atomize (full); auto)+
  
  lemma curry_shr: 
    "\<And>f g. (curry f \<equiv> g) \<equiv> (f \<equiv> uncurry g)"
    "\<And>f g. (curry0 f \<equiv> g) \<equiv> (f \<equiv> uncurry0 g)"
    by (atomize (full); auto)+
  
  lemmas uncurry_shl = curry_shr[symmetric]  
  lemmas uncurry_shr = curry_shl[symmetric]  
  




  (***************************************)
  (* Additions to Refine_Monadic *)
  


    ML \<open> (* TODO: Change in Refine_Automation! 
        The change is: Let extract_concrete_fun return definition and refinement theorem.
      *)
      structure Refine_Automation = struct
        open Refine_Automation

(* Recognize pattern of conclusion and extract term to make definition of *)
fun extract_concrete_fun _ [] concl = 
  raise TERM ("Conclusion does not match any extraction pattern",[concl])
  | extract_concrete_fun thy (pat::pats) concl = (
      case Refine_Util.fo_matchp thy pat concl of
        NONE => extract_concrete_fun thy pats concl
        | SOME [t] => t
        | SOME (t::_) => (
          warning ("concrete_definition: Pattern has multiple holes, taking "
            ^ "first one: " ^ @{make_string} pat
          ); t)
        | _ => (warning ("concrete_definition: Ignoring invalid pattern " 
             ^ @{make_string} pat);
             extract_concrete_fun thy pats concl)
    )
fun mk_qualified basename q = Binding.qualify true basename (Binding.name q);


      (* Define concrete function from refinement lemma *)
      fun define_concrete_fun gen_code fun_name attribs_raw param_names thm pats
        (orig_lthy:local_theory) = 
      let
        val lthy = orig_lthy;
        val ((inst,thm'),lthy) = yield_singleton2 (Variable.import true) thm lthy;
      
        val concl = thm' |> Thm.concl_of
      
        (*val ((typ_subst,term_subst),lthy) 
          = Variable.import_inst true [concl] lthy;
        val concl = Term_Subst.instantiate (typ_subst,term_subst) concl;
        *)
      
        val term_subst = #2 inst |> map (apsnd Thm.term_of) 
      
        val param_terms = map (fn name =>
          case AList.lookup (fn (n,v) => n = #1 v) term_subst name of
            NONE => raise TERM ("No such variable: "
                                 ^Term.string_of_vname name,[concl])
          | SOME t => t
        ) param_names;
      
        val f_term = extract_concrete_fun (Proof_Context.theory_of lthy) pats concl;
      
        val lhs_type = map Term.fastype_of param_terms ---> Term.fastype_of f_term;
        val lhs_term 
          = list_comb ((Free (Binding.name_of fun_name,lhs_type)),param_terms);
        val def_term = Logic.mk_equals (lhs_term,f_term) 
          |> fold Logic.all param_terms;
      
        val attribs = map (Attrib.check_src lthy) attribs_raw;
      
        val ((_,(_,def_thm)),lthy) = Specification.definition 
          (SOME (fun_name,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,attribs),def_term) lthy;
      
        val folded_thm = Local_Defs.fold lthy [def_thm] thm';
      
        val (_,lthy) 
          = Local_Theory.note 
             ((mk_qualified (Binding.name_of fun_name) "refine",[]),[folded_thm]) 
             lthy;
      
        val lthy = case gen_code of
          NONE => lthy
        | SOME modes => 
            extract_recursion_eqs modes (Binding.name_of fun_name) def_thm lthy
      
      in
        ((def_thm,folded_thm),lthy)
      end;


      end
    \<close>  

      
lemma rel2p_nres_RETURN[rel2p]: "rel2p (\<langle>A\<rangle>nres_rel) (RETURN x) (RETURN y) = rel2p A x y"   
  by (auto simp: rel2p_def dest: nres_relD intro: nres_relI)
      
      
  (* TODO: Move to Refine_Basic *)  
  lemma nres_rel_comp: "\<langle>A\<rangle>nres_rel O \<langle>B\<rangle>nres_rel = \<langle>A O B\<rangle>nres_rel"
    by (auto simp: nres_rel_def conc_fun_chain[symmetric] conc_trans)

  (* TODO: Move to Refine_Basic:Convenience lemmas *)  
  lemma (in -) ret_le_down_conv: 
    "nofail m \<Longrightarrow> RETURN c \<le> \<Down>R m \<longleftrightarrow> (\<exists>a. (c,a)\<in>R \<and> RETURN a \<le> m)"
    by (auto simp: pw_le_iff refine_pw_simps)
    
  (* TODO: Move to Refine_Basic *)  
  lemma param_ASSERT_bind[param]: "\<lbrakk> (\<Phi>,\<Psi>) \<in> bool_rel; \<lbrakk> \<Phi>; \<Psi> \<rbrakk> \<Longrightarrow> (f,g)\<in>\<langle>R\<rangle>nres_rel
    \<rbrakk> \<Longrightarrow> (ASSERT \<Phi> \<then> f, ASSERT \<Psi> \<then> g) \<in> \<langle>R\<rangle>nres_rel"
    by (auto intro: nres_relI)

  (* TODO: Move to Refine_Basic, convenience lemmas. Add to simpset?*)  
  lemma ASSERT_same_eq_conv: "(ASSERT \<Phi> \<then> m) = (ASSERT \<Phi> \<then> n) \<longleftrightarrow> (\<Phi> \<longrightarrow> m=n)"  
    by auto


  lemma case_prod_bind_simp[simp]: "
    (\<lambda>x. (case x of (a, b) \<Rightarrow> f a b) \<le> SPEC \<Phi>) = (\<lambda>(a,b). f a b \<le> SPEC \<Phi>)"
    by auto



  (* TODO: Move. More complete than leofD *)
  lemma (in -) le_by_leofI: "\<lbrakk> nofail m' \<Longrightarrow> nofail m; m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m \<le> m'"
    by (auto simp: pw_le_iff pw_leof_iff)

  (* TODO: Move *)  
  lemma (in -) leof_FAIL[simp]: "m \<le>\<^sub>n FAIL" by (auto simp: pw_leof_iff)

  lemma (in -) leof_fun_conv_le: 
    "(f x \<le>\<^sub>n M x) \<longleftrightarrow> (f x \<le> (if nofail (f x) then M x else FAIL))"
    by (auto simp: pw_le_iff pw_leof_iff)
    
  (* TODO: Move *)  
  lemma (in -) leof_add_nofailI: "\<lbrakk> nofail m \<Longrightarrow> m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m\<le>\<^sub>nm'"
    by (auto simp: pw_le_iff pw_leof_iff)
    

  lemma (in -) nofail_antimono_fun: "f \<le> g \<Longrightarrow> (nofail (g x) \<longrightarrow> nofail (f x))"
    by (auto simp: pw_le_iff pw_leof_iff dest: le_funD)

  (* TODO: Move near ASSERT_leof_rule *)  
  lemma (in -) leof_ASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n ASSERT \<Phi> \<then> m'"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma (in -) leof_ASSERT_refine_rule[refine]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n \<Down>R m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n \<Down>R (ASSERT \<Phi> \<then> m')"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma pw_nres_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nres_rel \<longleftrightarrow> nofail (\<Down> A b) \<longrightarrow> nofail a \<and> (\<forall>x. inres a x \<longrightarrow> inres (\<Down> A b) x)"
    by (simp add: pw_le_iff nres_rel_def)

  (* TODO: Move near RETURN_as_SPEC_refine *)  
  lemma RETURN_as_SPEC_refine_leof[refine2]:
    assumes "M \<le>\<^sub>n SPEC (\<lambda>c. (c,a)\<in>R)"
    shows "M \<le>\<^sub>n \<Down>R (RETURN a)"
    using assms
    by (simp add: pw_leof_iff refine_pw_simps)


  -- \<open>Order matters! \<close>
  lemmas [refine_vcg] = ASSERT_leI 
  lemmas [refine_vcg] = le_ASSUMEI 
  lemmas [refine_vcg] = le_ASSERTI 
  lemmas [refine_vcg] = ASSUME_leI


  (* TODO: Move to RefineG_Recursion (at least the removal of trimono-assumption) *)
  lemma RECT_eq_REC': "nofail (RECT B x) \<Longrightarrow> RECT B x = REC B x"
    apply (cases "trimono B")
    apply (subst RECT_eq_REC; simp_all add: nofail_def)
    unfolding RECT_def REC_def by simp

  (* TODO: Replace *)    
  thm REC_rule
  lemma REC_rule:
    fixes x::"'x"
    assumes M: "trimono body"
    assumes I0: "pre x"
    assumes IS: "\<And>f x. \<lbrakk> \<And>x. pre x \<Longrightarrow> f x \<le> M x; pre x; f \<le> REC body \<rbrakk> 
      \<Longrightarrow> body f x \<le> M x"
    shows "REC body x \<le> M x"
    by (rule REC_rule_arb[where pre="\<lambda>_. pre" and M="\<lambda>_. M", OF assms])


  (* TODO: Move to Refine_Basic convenience, near build_rel_SPEC *)  
  lemma build_rel_SPEC_conv: "\<Down>(br \<alpha> I) (SPEC \<Phi>) = SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
    by (auto simp: br_def pw_eq_iff refine_pw_simps)

  lemma build_rel_SPEC_leof: 
    assumes "m \<le>\<^sub>n SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
    shows "m \<le>\<^sub>n \<Down>(br \<alpha> I) (SPEC \<Phi>)"
    using assms by (auto simp: build_rel_SPEC_conv)
  
  (* TODO: Move to convenince lemmas ? *)
  lemma return_refine_prop_return:
    assumes "nofail m"
    assumes "RETURN x \<le> \<Down>R m"
    obtains x' where "(x,x')\<in>R" "RETURN x' \<le> m"
    using assms
    by (auto simp: refine_pw_simps pw_le_iff)

  (* TODO: Move to Refine_Basic:Convenience *)  
  lemma ignore_snd_refine_conv: 
    "(m \<le> \<Down>(R\<times>\<^sub>rUNIV) m') \<longleftrightarrow> m\<bind>(RETURN o fst) \<le>\<Down>R (m'\<bind>(RETURN o fst))"
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic:Convenience *)  
  lemma If_bind_distrib[simp]:
    fixes t e :: "'a nres"
    shows "(If b t e \<bind> (\<lambda>x. f x)) = (If b (t\<bind>(\<lambda>x. f x)) (e\<bind>(\<lambda>x. f x)))"  
    by simp

  (* TODO: Move to Refine_Basic: pw-reasoning *)  
  abbreviation "no_succ m \<equiv> (\<exists>x. inres m x)"

  (* TODO: Move to Refine_Basic: Convenience. 
    Can we make this a simproc, using NO_MATCH? *)  
  lemma unused_bind_conv: 
    assumes "NO_MATCH (ASSERT \<Phi>) m"
    assumes "NO_MATCH (ASSUME \<Phi>) m"
    shows "(m\<bind>(\<lambda>x. c))  = (ASSERT (nofail m) \<bind> (\<lambda>_. ASSUME (no_succ m) \<bind> (\<lambda>x. c)))" 
    by (auto simp: pw_eq_iff refine_pw_simps)


  (* TODO: Move *)  
  lemma FAIL_leof[simp, intro!]: "FAIL \<le>\<^sub>n m"  
    by (auto simp: le_or_fail_def)


lemma RECT_rule_leof:
  (*assumes M: "trimono body"*)
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "pre (x::'x)"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x'. \<lbrakk>pre x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le>\<^sub>n M x'; pre x; 
                        RECT body = f
    \<rbrakk> \<Longrightarrow> body f x \<le>\<^sub>n M x"
  shows "RECT body x \<le>\<^sub>n M x"
    apply (cases "\<not>trimono body")
    apply (simp add: RECT_def)
    using assms
    unfolding leof_fun_conv_le
    apply -
    apply (rule RECT_rule[where pre=pre and V=V])
    apply simp_all
    apply auto
    using gen_code_thm_RECT by fastforce

  (* TODO: REC_rule_leof! (However, this may require some fix 
       to the domain theory model of Refine_Monadic!) *)


  (* TODO: Move/Remove? *)
  lemma RELATES_nres_rel[refine_dref_RELATES]: "RELATES R \<Longrightarrow> RELATES (\<langle>R\<rangle>nres_rel)"
    by (simp add: RELATES_def)



  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma bind_sim_select_rule:
    assumes "m\<bind>f' \<le> SPEC \<Psi>"
    assumes "\<And>x. \<lbrakk>nofail m; inres m x; f' x\<le>SPEC \<Psi>\<rbrakk> \<Longrightarrow> f x\<le>SPEC \<Phi>"
    shows "m\<bind>f \<le> SPEC \<Phi>"
    -- \<open>Simultaneously select a result from assumption and verification goal.
      Useful to work with assumptions that restrict the current program to 
      be verified.\<close>
    using assms 
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma assert_bind_spec_conv: "ASSERT \<Phi> \<then> m \<le> SPEC \<Psi> \<longleftrightarrow> (\<Phi> \<and> m \<le> SPEC \<Psi>)"  
    -- \<open>Simplify a bind-assert verification condition. 
      Useful if this occurs in the assumptions, and considerably faster than 
      using pointwise reasoning, which may causes a blowup for many chained 
      assertions.\<close>
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to Refine_Basic: Convenience. *)
  lemma summarize_ASSERT_conv: "do {ASSERT \<Phi>; ASSERT \<Psi>; m} = do {ASSERT (\<Phi> \<and> \<Psi>); m}"
    by (auto simp: pw_eq_iff refine_pw_simps)
  
  (* TODO: Move: Refine_Basic: Convenience Lemmas *)
  lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAIL)"
    by auto
  

lemmas [refine] = nres_relI fun_relI (* TODO: Test this as default setup! *)

  (***************************************)
  (* Additions to Separation_Logic_Imperative_HOL *)

(* TODO: Move to Imperative/HOL. It's missing there! *)
lemma run_make[run_elims]:
  assumes "run (Array.make n f) \<sigma> \<sigma>' r"
          "\<not>is_exn \<sigma>"
  obtains "\<sigma>' = Some (snd (Array.alloc (map f [0 ..< n]) (the_state \<sigma>)))"
          "r = fst (Array.alloc (map f [0 ..< n]) (the_state \<sigma>))"
          "Array.get (the_state \<sigma>') r = (map f [0 ..< n])"
  using assms
  apply (cases \<sigma>)
  apply simp
  apply (auto simp add: run.simps)
  apply (simp add: execute_simps)
  apply (simp add: Array.get_alloc)
  apply hypsubst_thin
proof -
  case goal1
  from goal1(2) have "h' = snd (Array.alloc (map f [0 ..< n]) a)" 
    "r = fst (Array.alloc (map f [0 ..< n]) a)" by (auto simp add: execute_simps)
  from goal1(1)[OF this] show ?case .
qed

(* TODO: Move *)
lemma make_rule: "<emp> Array.make n f <\<lambda>r. r \<mapsto>\<^sub>a (map f [0 ..< n])>"
  unfolding hoare_triple_def snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemmas [sep_heap_rules] = make_rule

(* Move to Array_Blit. Are there system-calls for array-copy? *)
definition "array_copy a \<equiv> do {
  l\<leftarrow>Array.len a;
  if l=0 then 
    Array.of_list []
  else do {
    s \<leftarrow> Array.nth a 0;
    a'\<leftarrow>Array.new l s;
    blit a 0 a' 0 l;
    return a'
  }
}"

lemma array_copy_rule[sep_heap_rules]:
  "
    < a\<mapsto>\<^sub>al> 
      array_copy a 
    <\<lambda>a'. a\<mapsto>\<^sub>al * a'\<mapsto>\<^sub>a l>"
  unfolding array_copy_def
  by sep_auto


lemma mod_starD: "h\<Turnstile>A*B \<Longrightarrow> \<exists>h1 h2. h1\<Turnstile>A \<and> h2\<Turnstile>B"
  by (auto simp: mod_star_conv)

(* TODO: Move *)  
lemma star_or_dist1: 
  "(A \<or>\<^sub>A B)*C = (A*C \<or>\<^sub>A B*C)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 
  
lemma star_or_dist2: 
  "C*(A \<or>\<^sub>A B) = (C*A \<or>\<^sub>A C*B)"  
  apply (rule ent_iffI) 
  unfolding entails_def
  by (auto simp add: mod_star_conv) 

lemmas star_or_dist = star_or_dist1 star_or_dist2  

lemma ent_disjI1': "A\<Longrightarrow>\<^sub>AB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_disjI2': "A\<Longrightarrow>\<^sub>AC \<Longrightarrow> A\<Longrightarrow>\<^sub>AB\<or>\<^sub>AC"
  by (auto simp: entails_def star_or_dist)

lemma ent_star_mono_true: 
  assumes "A \<Longrightarrow>\<^sub>A A' * true"
  assumes "B \<Longrightarrow>\<^sub>A B' * true"
  shows "A*B*true \<Longrightarrow>\<^sub>A A'*B'*true"
  using ent_star_mono[OF assms] apply simp
  using ent_true_drop(1) by blast

lemma ent_refl_true: "A \<Longrightarrow>\<^sub>A A * true"
  by (simp add: ent_true_drop(2)) 

(* TODO: Move, this is a quite general concept *)
text \<open>Weakening of entails to allow arbitrary unspecified memory in conclusion\<close>
definition entailst :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>t" 10)
  where "entailst A B \<equiv> A \<Longrightarrow>\<^sub>A B * true"

lemma enttI: "A\<Longrightarrow>\<^sub>AB*true \<Longrightarrow> A\<Longrightarrow>\<^sub>tB" unfolding entailst_def .
lemma enttD: "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>AB*true" unfolding entailst_def .

(* TODO: Can we change the patterns of assn_simproc to add this pattern? *)
simproc_setup assn_simproc_entt ("\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>'")
  = {*K Seplogic_Auto.assn_simproc_fun*}


lemma entt_trans:
  "entailst A B \<Longrightarrow> entailst B C \<Longrightarrow> entailst A C"
  unfolding entailst_def
  apply (erule ent_trans)
  apply (erule ent_frame_fwd)
  apply (rule ent_refl)
  apply solve_entails
  done

lemma entt_refl[simp, intro!]: "entailst A A"
  unfolding entailst_def by sep_auto

lemma entt_true[simp, intro!]:
  "entailst A true"
  unfolding entailst_def by sep_auto

lemma entt_emp[simp, intro!]:
  "entailst A emp"
  unfolding entailst_def by sep_auto

lemma entt_star_true_simp[simp]:
  "entailst A (B*true) \<longleftrightarrow> entailst A B"
  "entailst (A*true) B \<longleftrightarrow> entailst A B"
  unfolding entailst_def 
    apply -
    apply sep_auto
    subgoal 
      apply (rule iffI)
      subgoal using ent_refl_true ent_trans by blast
      subgoal by (erule ent_frame_fwd, frame_inference) solve_entails
    done  
  done

lemma entt_star_mono: "\<lbrakk>entailst A B; entailst C D\<rbrakk> \<Longrightarrow> entailst (A*C) (B*D)"
  unfolding entailst_def
  apply (erule ent_frame_fwd, frame_inference)
  apply (erule ent_frame_fwd, frame_inference)
  by solve_entails

lemma entt_frame_fwd:
  assumes "entailst P Q"
  assumes "entailst A (P*F)"
  assumes "entailst (Q*F) B"
  shows "entailst A B"
  using assms
  by (metis entt_refl entt_star_mono entt_trans)

lemma enttI_true: "P*true \<Longrightarrow>\<^sub>A Q*true \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ"
  by (drule enttI) simp

lemma entt_def_true: "(P\<Longrightarrow>\<^sub>tQ) \<equiv> (P*true \<Longrightarrow>\<^sub>A Q*true)"
  unfolding entailst_def
  apply (rule eq_reflection)
  subgoal 
    apply (rule iffI)
    subgoal by (erule ent_frame_fwd, frame_inference) solve_entails
    subgoal using ent_refl_true ent_trans by blast
  done  
  done

lemma ent_imp_entt: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>tQ" 
  apply (rule enttI)
  apply (erule ent_trans)
  by sep_auto

lemma cons_rulet: "\<lbrakk>P\<Longrightarrow>\<^sub>tP'; \<And>x. Q x \<Longrightarrow>\<^sub>t Q' x; <P'> c <Q>\<^sub>t \<rbrakk> \<Longrightarrow> <P> c <Q'>\<^sub>t"
  unfolding entailst_def
  apply (rule cons_pre_rule)
  apply assumption
  apply (rule cons_post_rule)
  apply (erule frame_rule)
  apply simp
  subgoal for x
    apply (rule ent_frame_fwd[of "Q x"])
    apply assumption
    apply (rule ent_refl)
    apply solve_entails
  done  
  done

lemmas cons_pre_rulet = cons_rulet[OF _ entt_refl]
lemmas cons_post_rulet = cons_rulet[OF entt_refl, rotated]

lemma entt_fr_refl: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'*A" by (rule entt_star_mono) auto
lemma entt_fr_drop: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'"
  using ent_true_drop(1) enttD enttI by blast 


(* TODO: Naming scheme of these thms is chaotic *)

lemma ent_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)

lemma ent_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>A A \<or>\<^sub>A B"
  by (simp add: entails_def)

lemma entt_disjI1_direct[simp]: "A \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI1_direct])

lemma entt_disjI2_direct[simp]: "B \<Longrightarrow>\<^sub>t A \<or>\<^sub>A B"
  by (rule ent_imp_entt[OF ent_disjI2_direct])

lemma entt_disjI1': "A\<Longrightarrow>\<^sub>tB \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjI2': "A\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tB\<or>\<^sub>AC"
  by (auto simp: entailst_def entails_def star_or_dist)

lemma entt_disjE: "\<lbrakk> A\<Longrightarrow>\<^sub>tM; B\<Longrightarrow>\<^sub>tM \<rbrakk> \<Longrightarrow> A\<or>\<^sub>AB \<Longrightarrow>\<^sub>t M"
  using ent_disjE enttD enttI by blast  
    
lemma entt_disjD1: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> A\<Longrightarrow>\<^sub>tC"
  using entt_disjI1_direct entt_trans by blast

lemma entt_disjD2: "A\<or>\<^sub>AB\<Longrightarrow>\<^sub>tC \<Longrightarrow> B\<Longrightarrow>\<^sub>tC"
  using entt_disjI2_direct entt_trans by blast



definition "is_pure_assn a \<equiv> \<exists>P. a=\<up>P"
lemma is_pure_assnE: assumes "is_pure_assn a" obtains P where "a=\<up>P"
  using assms
  by (auto simp: is_pure_assn_def)

lemma is_pure_assn_pure[simp, intro!]: "is_pure_assn (\<up>P)" by (simp add: is_pure_assn_def)

lemma is_pure_assn_basic_simps[simp]:
  "is_pure_assn false"
  "is_pure_assn emp"
proof -
  have "is_pure_assn (\<up>False)" by rule thus "is_pure_assn false" by simp
  have "is_pure_assn (\<up>True)" by rule thus "is_pure_assn emp" by simp
qed  

lemma is_pure_assn_starI[simp,intro!]: "\<lbrakk>is_pure_assn a; is_pure_assn b\<rbrakk> \<Longrightarrow> is_pure_assn (a*b)"
  by (auto elim!: is_pure_assnE)







end
