section {* Deterministic Monad *}
theory Refine_Det
imports 
  "~~/src/HOL/Library/Monad_Syntax"
  "Generic/RefineG_Assert"
  "Generic/RefineG_While"
begin

subsection {* Deterministic Result Lattice *}
text {*
  We define the flat complete lattice of deterministic program results:
*}
(* TODO: Library/Quickcheck_Types.thy:flat_complete_lattice provides
  an isomorphic contruction. *)
datatype 'a dres = 
  dSUCCEEDi   -- "No result"
| dFAILi      -- "Failure"
| dRETURN 'a  -- "Regular result"

instantiation dres :: (type) complete_lattice
begin
  definition "top_dres \<equiv> dFAILi"
  definition "bot_dres \<equiv> dSUCCEEDi"
  fun sup_dres where
    "sup dFAILi _ = dFAILi" |
    "sup _ dFAILi = dFAILi" |
    "sup (dRETURN a) (dRETURN b) = (if a=b then dRETURN b else dFAILi)" |
    "sup dSUCCEEDi x = x" | 
    "sup x dSUCCEEDi = x"

  lemma sup_dres_addsimps[simp]:
    "sup x dFAILi = dFAILi"
    "sup x dSUCCEEDi = x"
    apply (case_tac [!] x)
    apply simp_all
    done

  fun inf_dres where
    "inf dFAILi x = x" |
    "inf x dFAILi = x" |
    "inf (dRETURN a) (dRETURN b) = (if a=b then dRETURN b else dSUCCEEDi)" |
    "inf dSUCCEEDi _ = dSUCCEEDi" | 
    "inf _ dSUCCEEDi = dSUCCEEDi"

  lemma inf_dres_addsimps[simp]:
    "inf x dSUCCEEDi = dSUCCEEDi"
    "inf x dFAILi = x"
    apply (case_tac [!] x)
    apply simp_all
    done

  definition "Sup_dres S \<equiv> 
    if S\<subseteq>{dSUCCEEDi} then dSUCCEEDi 
    else if dFAILi\<in>S then dFAILi
    else if \<exists>a b. a\<noteq>b \<and> dRETURN a\<in>S \<and> dRETURN b\<in>S then dFAILi
    else dRETURN (THE x. dRETURN x \<in> S)"

  definition "Inf_dres S \<equiv> 
    if S\<subseteq>{dFAILi} then dFAILi 
    else if dSUCCEEDi\<in>S then dSUCCEEDi
    else if \<exists>a b. a\<noteq>b \<and> dRETURN a\<in>S \<and> dRETURN b\<in>S then dSUCCEEDi
    else dRETURN (THE x. dRETURN x \<in> S)"
  
  fun less_eq_dres where
    "less_eq_dres dSUCCEEDi _ \<longleftrightarrow> True" |
    "less_eq_dres _ dFAILi \<longleftrightarrow> True" |
    "less_eq_dres (dRETURN (a::'a)) (dRETURN b) \<longleftrightarrow> a=b" |
    "less_eq_dres _ _ \<longleftrightarrow> False"

  definition less_dres where "less_dres (a::'a dres) b \<longleftrightarrow> a\<le>b \<and> \<not> b\<le>a"

  instance
    apply intro_classes
    apply (simp add: less_dres_def)
    apply (case_tac x, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, 
      simp_all, case_tac [!] z, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, 
      simp_all, case_tac [!] z, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, simp_all) []

    apply (case_tac x, simp_all, case_tac [!] y, 
      simp_all, case_tac [!] z, simp_all) []

    apply (case_tac x, auto simp: Inf_dres_def) []

    apply (case_tac z, simp_all add: Inf_dres_def) []
      apply (auto) [] 
        apply (case_tac x, fastforce+) []
        apply (case_tac x, fastforce+) []
        
      apply auto []
        apply (case_tac x) 
          apply force 
          apply force
          apply (metis less_eq_dres.simps(4))
        apply force

        apply (case_tac x) [] 
          apply force
          apply force
          apply auto []
          apply (rename_tac aa)
          apply (subgoal_tac "(THE x. dRETURN x \<in> A) = aa")
          apply force
          apply force

    apply (case_tac x)
    apply (auto simp add: Sup_dres_def) [3]
    apply (case_tac xa, simp_all) [] 
    apply (rename_tac aa)
    apply (subgoal_tac "(THE x. dRETURN x \<in> A) = aa")
    apply force
    apply force

    apply (case_tac z, auto simp add: Sup_dres_def) []
      apply force
      apply (case_tac x, force+) []

      apply (case_tac x, force, force) []
      apply (metis Refine_Det.less_eq_dres.simps(4))

      apply force

      apply (case_tac x, force+)[]

      apply (auto simp: top_dres_def Inf_dres_def)

      apply (auto simp: bot_dres_def Sup_dres_def)
  done

end

abbreviation "dSUCCEED \<equiv> (bot::'a dres)"
abbreviation "dFAIL \<equiv> (top::'a dres)"

lemma dres_cases[cases type, case_names dSUCCEED dRETURN dFAIL]:
  obtains "x=dSUCCEED" | r where "x=dRETURN r" | "x=dFAIL" 
  unfolding bot_dres_def top_dres_def by (cases x) auto

lemmas [simp] = dres.case(1,2)[folded top_dres_def bot_dres_def]

lemma dres_order_simps[simp]:
  "x\<le>dSUCCEED \<longleftrightarrow> x=dSUCCEED" 
  "dFAIL\<le>x \<longleftrightarrow> x=dFAIL"
  "dRETURN r \<noteq> dFAIL"
  "dRETURN r \<noteq> dSUCCEED"
  "dFAIL \<noteq> dRETURN r"
  "dSUCCEED \<noteq> dRETURN r"
  "dFAIL\<noteq>dSUCCEED"
  "dSUCCEED\<noteq>dFAIL"
  "x=y \<Longrightarrow> inf (dRETURN x) (dRETURN y) = dRETURN y"
  "x\<noteq>y \<Longrightarrow> inf (dRETURN x) (dRETURN y) = dSUCCEED"
  "x=y \<Longrightarrow> sup (dRETURN x) (dRETURN y) = dRETURN y"
  "x\<noteq>y \<Longrightarrow> sup (dRETURN x) (dRETURN y) = dFAIL"
  apply (simp_all add: bot_unique top_unique) 
  apply (simp_all add: bot_dres_def top_dres_def)
  done

lemma dres_Sup_cases:
  obtains "S\<subseteq>{dSUCCEED}" and "Sup S = dSUCCEED"
  | "dFAIL\<in>S" and "Sup S = dFAIL"
  | a b where "a\<noteq>b" "dRETURN a\<in>S" "dRETURN b\<in>S" "dFAIL\<notin>S" "Sup S = dFAIL"
  | a where "S \<subseteq> {dSUCCEED, dRETURN a}" "dRETURN a\<in>S" "Sup S = dRETURN a"
proof -
  show ?thesis
    apply (cases "S\<subseteq>{dSUCCEED}")
    apply (rule that(1), assumption)
    apply (simp add: Sup_dres_def bot_dres_def)

    apply (cases "dFAIL\<in>S")
    apply (rule that(2), assumption)
    apply (simp add: Sup_dres_def bot_dres_def top_dres_def)

    apply (cases "\<exists>a b. a\<noteq>b \<and> dRETURN a\<in>S \<and> dRETURN b\<in>S")
    apply (elim exE conjE)
    apply (rule that(3), assumption+)
    apply (auto simp add: Sup_dres_def bot_dres_def top_dres_def) []

    apply simp
    apply (cases "\<exists>a. dRETURN a \<in> S")
    apply (elim exE)
    apply (rule_tac a=a in that(4)) []
    apply auto [] apply (case_tac xa, auto) []
    apply auto []
    apply (auto simp add: Sup_dres_def bot_dres_def top_dres_def) []

    apply auto apply (case_tac x, auto) []
    done
qed

lemma dres_Inf_cases:
  obtains "S\<subseteq>{dFAIL}" and "Inf S = dFAIL"
  | "dSUCCEED\<in>S" and "Inf S = dSUCCEED"
  | a b where "a\<noteq>b" "dRETURN a\<in>S" "dRETURN b\<in>S" "dSUCCEED\<notin>S" "Inf S = dSUCCEED"
  | a where "S \<subseteq> {dFAIL, dRETURN a}" "dRETURN a\<in>S" "Inf S = dRETURN a"
proof -
  show ?thesis
    apply (cases "S\<subseteq>{dFAIL}")
    apply (rule that(1), assumption)
    apply (simp add: Inf_dres_def top_dres_def)

    apply (cases "dSUCCEED\<in>S")
    apply (rule that(2), assumption)
    apply (simp add: Inf_dres_def bot_dres_def top_dres_def)

    apply (cases "\<exists>a b. a\<noteq>b \<and> dRETURN a\<in>S \<and> dRETURN b\<in>S")
    apply (elim exE conjE)
    apply (rule that(3), assumption+)
    apply (auto simp add: Inf_dres_def bot_dres_def top_dres_def) []

    apply simp
    apply (cases "\<exists>a. dRETURN a \<in> S")
    apply (elim exE)
    apply (rule_tac a=a in that(4)) []
    apply auto [] apply (case_tac xa, auto) []
    apply auto []
    apply (auto simp add: Inf_dres_def bot_dres_def top_dres_def) []

    apply auto apply (case_tac x, auto) []
    done
qed

lemma dres_chain_eq_res:
  "is_chain M \<Longrightarrow> 
    dRETURN r \<in> M \<Longrightarrow> dRETURN s \<in> M \<Longrightarrow> r=s"
  by (metis chainD less_eq_dres.simps(4))

lemma dres_Sup_chain_cases:
  assumes CHAIN: "is_chain M"
  obtains "M \<subseteq> {dSUCCEED}" "Sup M = dSUCCEED"
  | r where "M \<subseteq> {dSUCCEED,dRETURN r}" "dRETURN r\<in>M" "Sup M = dRETURN r"
  | "dFAIL\<in>M" "Sup M = dFAIL"
  apply (rule dres_Sup_cases[of M])
  using dres_chain_eq_res[OF CHAIN]
  by auto

lemma dres_Inf_chain_cases:
  assumes CHAIN: "is_chain M"
  obtains "M \<subseteq> {dFAIL}" "Inf M = dFAIL"
  | r where "M \<subseteq> {dFAIL,dRETURN r}" "dRETURN r\<in>M" "Inf M = dRETURN r"
  | "dSUCCEED\<in>M" "Inf M = dSUCCEED"
  apply (rule dres_Inf_cases[of M])
  using dres_chain_eq_res[OF CHAIN]
  by auto

lemma dres_internal_simps[simp]:
  "dSUCCEEDi = dSUCCEED"
  "dFAILi = dFAIL"
  unfolding top_dres_def bot_dres_def by auto
 
subsubsection {* Monad Operations *}
function dbind where 
  "dbind dFAIL _ = dFAIL"
| "dbind dSUCCEED _ = dSUCCEED"
| "dbind (dRETURN x) f = f x"
  unfolding bot_dres_def top_dres_def
  by pat_completeness auto
termination by lexicographic_order

adhoc_overloading
  Monad_Syntax.bind dbind

lemma [code]:
  "dbind (dRETURN x) f = f x"
  "dbind (dSUCCEEDi) f = dSUCCEEDi"
  "dbind (dFAILi) f = dFAILi"
  by simp_all

lemma dres_monad1[simp]: "dbind (dRETURN x) f = f x"
  by (simp)
lemma dres_monad2[simp]: "dbind M dRETURN = M"
  apply (cases M)
  apply (auto)
  done

lemma dres_monad3[simp]: "dbind (dbind M f) g = dbind M (\<lambda>x. dbind (f x) g)"
  apply (cases M)
  apply auto
  done

lemmas dres_monad_laws = dres_monad1 dres_monad2 dres_monad3

lemma dbind_mono[refine_mono]:
  "\<lbrakk> M \<le> M'; \<And>x. dRETURN x \<le> M \<Longrightarrow> f x \<le> f' x \<rbrakk> \<Longrightarrow> dbind M f \<le> dbind M' f'"
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (dbind M f) (dbind M' f')"
  apply (cases M, simp_all)
  apply (cases M', simp_all)
  apply (cases M, simp_all add: flat_ord_def)
  apply (cases M', simp_all)
  done

lemma dbind_mono1[simp, intro!]: "mono dbind"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule dbind_mono)
  by auto

lemma dbind_mono2[simp, intro!]: "mono (dbind M)"
  apply (rule monoI)
  apply (rule dbind_mono)
  by (auto dest: le_funD)

lemma dr_mono_bind:
  assumes MA: "mono A" and MB: "\<And>s. mono (B s)"
  shows "mono (\<lambda>F s. dbind (A F s) (\<lambda>s'. B s F s'))"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule dbind_mono)
  apply (auto dest: monoD[OF MA, THEN le_funD]) []
  apply (auto dest: monoD[OF MB, THEN le_funD]) []
  done

lemma dr_mono_bind': "mono (\<lambda>F s. dbind (f s) F)"
  apply rule
  apply (rule le_funI)
  apply (rule dbind_mono)
  apply (auto dest: le_funD)
  done

(* TODO: Replace by monotonicity prover! *)
lemmas dr_mono = mono_if dr_mono_bind dr_mono_bind' mono_const mono_id

lemma [refine_mono]:
  "dbind dSUCCEED f = dSUCCEED"
  "dbind dFAIL f = dFAIL"
  by (simp_all)

definition "dASSERT \<equiv> iASSERT dRETURN"
definition "dASSUME \<equiv> iASSUME dRETURN"
interpretation dres_assert: generic_Assert dbind dRETURN dASSERT dASSUME
  apply unfold_locales
  by (auto simp: dASSERT_def dASSUME_def)

definition "dWHILEIT \<equiv> iWHILEIT dbind dRETURN"
definition "dWHILEI \<equiv> iWHILEI dbind dRETURN"
definition "dWHILET \<equiv> iWHILET dbind dRETURN"
definition "dWHILE \<equiv> iWHILE dbind dRETURN"

interpretation dres_while: generic_WHILE dbind dRETURN
  dWHILEIT dWHILEI dWHILET dWHILE
  apply unfold_locales
  apply (auto simp: dWHILEIT_def dWHILEI_def dWHILET_def dWHILE_def) 
  apply refine_mono+
  done

lemmas [code] = 
  dres_while.WHILEIT_unfold
  dres_while.WHILEI_unfold
  dres_while.WHILET_unfold
  dres_while.WHILE_unfold


text {* 
  Syntactic criteria to prove @{text "s \<noteq> dSUCCEED"}
*}
lemma dres_ne_bot_basic[refine_transfer]:
  "dFAIL \<noteq> dSUCCEED"
  "\<And>x. dRETURN x \<noteq> dSUCCEED"
  "\<And>m f. \<lbrakk> m\<noteq>dSUCCEED; \<And>x. f x \<noteq> dSUCCEED \<rbrakk> \<Longrightarrow> dbind m f \<noteq> dSUCCEED"
  "\<And>\<Phi>. dASSERT \<Phi> \<noteq> dSUCCEED"
  "\<And>b m1 m2. \<lbrakk> m1\<noteq>dSUCCEED; m2\<noteq>dSUCCEED \<rbrakk> \<Longrightarrow> If b m1 m2 \<noteq> dSUCCEED"
  "\<And>x f. \<lbrakk> \<And>x. f x\<noteq>dSUCCEED \<rbrakk> \<Longrightarrow> Let x f \<noteq> dSUCCEED"
  "\<And>g p. \<lbrakk> \<And>x1 x2. g x1 x2 \<noteq> dSUCCEED \<rbrakk> \<Longrightarrow> case_prod g p \<noteq> dSUCCEED"
  "\<And>fn fs x. 
    \<lbrakk> fn\<noteq>dSUCCEED; \<And>v. fs v \<noteq> dSUCCEED \<rbrakk> \<Longrightarrow> case_option fn fs x \<noteq> dSUCCEED"
  "\<And>fn fc x. 
    \<lbrakk> fn\<noteq>dSUCCEED; \<And>x xs. fc x xs \<noteq> dSUCCEED \<rbrakk> \<Longrightarrow> case_list fn fc x \<noteq> dSUCCEED"
  apply (auto split: prod.split option.split list.split)
  apply (case_tac m, auto) []
  apply (case_tac \<Phi>, auto) []
  done
  
lemma dres_ne_bot_RECT[refine_transfer]:
  assumes A: "\<And>f x. \<lbrakk> \<And>x. f x \<noteq> dSUCCEED \<rbrakk> \<Longrightarrow> B f x \<noteq> dSUCCEED"
  shows "RECT B x \<noteq> dSUCCEED"
  unfolding RECT_def
  apply (split split_if)
  apply (intro impI conjI)
  apply simp_all
  
  apply (rule flatf_fp_induct_pointwise[where pre="\<lambda>_ _. True" and B=B and b=top and post="\<lambda>_ _ m. m\<noteq>dSUCCEED"])
  apply (simp_all add: trimonoD A)
  done

lemma dres_ne_bot_dWHILEIT[refine_transfer]:
  assumes "\<And>x. f x \<noteq> dSUCCEED" 
  shows "dWHILEIT I b f s \<noteq> dSUCCEED" using assms
  unfolding dWHILEIT_def iWHILEIT_def WHILEI_body_def
  apply refine_transfer
  done

lemma dres_ne_bot_dWHILET[refine_transfer]:
  assumes "\<And>x. f x \<noteq> dSUCCEED" 
  shows "dWHILET b f s \<noteq> dSUCCEED" using assms
  unfolding dWHILET_def iWHILET_def iWHILEIT_def WHILEI_body_def
  apply refine_transfer
  done

end
