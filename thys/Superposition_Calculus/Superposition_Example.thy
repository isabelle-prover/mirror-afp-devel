theory Superposition_Example
  imports
    Superposition
    IsaFoR_Term_Copy
    VeriComp.Well_founded
begin

lemma asymp_bot [iff]: "asymp \<bottom>"
  by (simp add: asymp_on_def)

lemma transp_bot [iff]: "transp \<bottom>"
  by (simp add: transp_def)

lemma wfp_bot [iff]: "wfp \<bottom>"
  by (simp add: wfp_def)

sublocale nonground_term_with_context \<subseteq>
  nonground_term_order "less_kbo :: ('f :: weighted,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
proof unfold_locales
   show "transp less_kbo"
    using KBO.S_trans
    unfolding transp_def less_kbo_def
    by blast
next
  show "asymp less_kbo"
    using wfp_imp_asymp wfP_less_kbo
    by blast
next
  show "wfp_on (range term.from_ground) less_kbo"
    using wfp_on_subset[OF wfP_less_kbo subset_UNIV] .
next
  show "totalp_on (range term.from_ground) less_kbo"
    using less_kbo_gtotal
    unfolding totalp_on_def Term.ground_vars_term_empty term.is_ground_iff_range_from_ground
    by blast
next
  fix
    c :: "('f, 'v) context" and
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo c\<langle>t\<^sub>1\<rangle> c\<langle>t\<^sub>2\<rangle>"
    unfolding less_kbo_def
    by (rule KBO.S_ctxt)
next
  fix
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term" and
    \<gamma> :: "('f, 'v) subst"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo (t\<^sub>1 \<cdot>t \<gamma>) (t\<^sub>2 \<cdot>t \<gamma>)"
    by (rule less_kbo_subst)
next
  fix t and c :: "('f, 'v) context"
  assume "c \<noteq> \<box>"

  then show "less_kbo t c\<langle>t\<rangle>"
    unfolding less_kbo_def
    by (intro KBO.S_supt nectxt_imp_supt_ctxt)
qed

(* TODO: use strictly_generalizes *)
abbreviation trivial_tiebreakers :: 
  "'f gatom clause \<Rightarrow> ('f,'v) atom clause \<Rightarrow> ('f,'v) atom clause \<Rightarrow> bool" where
  "trivial_tiebreakers \<equiv> \<bottom>"

(* TODO: We have to get the ground_critical_pair_theorem into the afp *)
locale trivial_superposition_example =
  ground_critical_pair_theorem "TYPE('f :: weighted)"
begin

(* TODO: Why is this needed? *)
sublocale nonground_clause .

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation unit_typing where
  "unit_typing _ _ \<equiv> ([], ())"
                                           
sublocale
  superposition_calculus where
    select = "trivial_select :: (('f , 'v :: infinite) atom) select" and
    less\<^sub>t = less_kbo and
    \<F> = unit_typing and
    tiebreakers = trivial_tiebreakers
  by unfold_locales auto

end

context nonground_order
begin

abbreviation select_max where
  "select_max C \<equiv>
    if \<exists>l\<in>#C. is_maximal l C \<and> is_neg l
    then {#SOME l. is_maximal l C \<and> is_neg l#}
    else {#}"

sublocale select_max: selection_function select_max
proof unfold_locales
  fix C

  {
    assume "\<exists>l\<in>#C. is_maximal l C \<and> is_neg l" 

    then have "\<exists>l. is_maximal l C \<and> is_neg l"
      by blast
  
    then have "(SOME l. is_maximal l C \<and> is_neg l) \<in># C"
      by (rule someI2_ex) (simp add: maximal_in_clause)
  }

  then show "select_max C \<subseteq># C"
    by auto
next
  fix C l

  {
    assume "\<exists>l\<in>#C. is_maximal l C \<and> is_neg l" 

    then have "\<exists>l. is_maximal l C \<and> is_neg l"
      by blast
  
    then have "is_neg (SOME l. is_maximal l C \<and> is_neg l)"
      by (rule someI2_ex) simp
  }

  then show "l \<in># select_max C \<Longrightarrow> is_neg l"
    by (smt (verit, ccfv_threshold) ex_in_conv set_mset_add_mset_insert set_mset_eq_empty_iff 
        singletonD)
qed

end

abbreviation pr_strict :: "('f :: wellorder \<times> nat) \<Rightarrow> _ \<Rightarrow> bool" where
  "pr_strict \<equiv> lex_prodp ((<) :: 'f \<Rightarrow> 'f \<Rightarrow> bool) ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"

lemma wfp_pr_strict: "wfp pr_strict"
  by (simp add: lex_prodp_wfP)

abbreviation least where
  "least x \<equiv> \<forall>y. x \<le> y"

abbreviation weight :: "'f \<times> nat \<Rightarrow> nat" where
  "weight _ \<equiv> 1"

abbreviation weights where 
  "weights \<equiv> \<lparr>w = weight, w0 = 1, pr_strict = pr_strict\<inverse>\<inverse>, least = least, scf = \<lambda>_ _. 1\<rparr>"

instantiation nat :: weighted begin

definition weights_nat :: "nat weights" where
  "weights_nat \<equiv> weights"

instance
proof -

  have "SN {(fn  :: nat \<times> nat, gm). fst gm < fst fn \<or> fst gm = fst fn \<and> snd gm < snd fn}"
  proof (fold lex_prodp_def, rule wf_imp_SN)
  
    show "wf ({(fn, gm). pr_strict gm fn}\<inverse>)"
      using wfp_pr_strict
      by (simp add: converse_def wfp_def)
  qed

  then show "OFCLASS(nat, weighted_class)"
    by (intro_classes, unfold weights_nat_def lex_prodp_def admissible_kbo_def) 
       (auto simp: order.order_iff_strict)
qed

end

instantiation nat :: infinite 
begin

instance
  by intro_classes simp

end

datatype type = A | B

abbreviation types :: "nat \<Rightarrow> nat \<Rightarrow> type list \<times> type" where
  "types f n \<equiv>
    let type = if even f then A else B
    in (replicate n type, type)"

lemma types_inhabited: "\<exists>f. types f 0 = ([], \<tau>)"
proof (cases \<tau>)
  case A
  show ?thesis
    unfolding A
    by (rule exI[of _ 0]) auto
next
  case B
  show ?thesis
    unfolding B
    by (rule exI[of _ 1]) auto
qed

locale superposition_example =
  ground_critical_pair_theorem "TYPE(nat)"
begin

sublocale nonground_term_with_context .

sublocale nonground_order less_kbo
  by unfold_locales

sublocale
  superposition_calculus
    "select_max :: (nat, nat) atom select"
    less_kbo
    types
    trivial_tiebreakers
proof unfold_locales
  fix \<tau>
  show "\<exists>f. types f 0 = ([], \<tau>)"
    using types_inhabited .
qed simp_all

end

end
