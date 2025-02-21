theory Superposition_Example
  imports
    Superposition
    IsaFoR_Term_Copy
    VeriComp.Well_founded
begin

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
    using KBO.S_ctxt less_kbo_def
    by blast
next
  fix
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term" and
    \<gamma> :: "('f, 'v) subst"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo (t\<^sub>1 \<cdot>t \<gamma>) (t\<^sub>2 \<cdot>t \<gamma>)"
    using less_kbo_subst by blast
next
  fix
    t :: "('f, 'v) term" and
    c :: "('f, 'v) context"
  assume
    "term.is_ground t"
    "context.is_ground c"
    "c \<noteq> \<box>"

  then show "less_kbo t c\<langle>t\<rangle>"
    by (simp add: KBO.S_supt less_kbo_def nectxt_imp_supt_ctxt)
qed

(* TODO: use strictly_generalizes *)
abbreviation trivial_tiebreakers :: 
  "'f gatom clause \<Rightarrow> ('f,'v) atom clause \<Rightarrow> ('f,'v) atom clause \<Rightarrow> bool" where
  "trivial_tiebreakers _ _ _ \<equiv> False"

lemma trivial_tiebreakers: "wellfounded_strict_order (trivial_tiebreakers C\<^sub>G)"
  by unfold_locales auto

(* TODO: We have to get the ground_critical_pair_theorem into the afp *)
locale trivial_superposition_example =
  ground_critical_pair_theorem "TYPE('f :: weighted)"
begin

sublocale nonground_term_with_context.

abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation unit_types where
  "unit_types _ \<equiv> ([], ())"

sublocale selection_function trivial_select
  by unfold_locales auto
                                           
sublocale
  superposition_calculus
    "trivial_select :: ('f , 'v :: infinite) select"
    less_kbo
    unit_types
    trivial_tiebreakers
  by unfold_locales (auto simp: UNIV_unit)

end

context nonground_equality_order
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
      by(rule someI2_ex) (simp add: maximal_in_clause)
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


datatype type = A | B

lemma UNIV_type [simp]: "(UNIV :: type set) = {A, B}"
  using type.exhaust by blast

lemma UNIV_type_ordLeq_UNIV_nat: "|UNIV :: type set| \<le>o |UNIV :: nat set|"
  by (simp add: ordLeq3_finite_infinite)

definition pr_strict :: "('f :: wellorder \<times> nat) \<Rightarrow> _ \<Rightarrow> bool" where
  "pr_strict = lex_prodp ((<) :: 'f \<Rightarrow> 'f \<Rightarrow> bool) ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"

lemma wfp_pr_strict: "wfp pr_strict"
  by (simp add: lex_prodp_wfP pr_strict_def)

lemma transp_pr_strict: "transp pr_strict"
proof (rule transpI)
  show "\<And>x y z. pr_strict x y \<Longrightarrow> pr_strict y z \<Longrightarrow> pr_strict x z"
    unfolding pr_strict_def lex_prodp_def
    by force
qed

definition least where
  "least x \<longleftrightarrow> (\<forall>y. x \<le> y)"

definition weight :: "'f \<times> nat \<Rightarrow> nat" where
  "weight p = 1" 

abbreviation weights where "weights \<equiv>
  \<lparr>w = weight, w0 = 1, pr_strict = pr_strict\<inverse>\<inverse>, least = least, scf = \<lambda>_ _. 1\<rparr>"
                                  
interpretation weighted weights
proof (unfold_locales, unfold weights.select_convs weight_def least_def pr_strict_def lex_prodp_def)
 
  show "SN {(fn  :: ('b :: wellorder) \<times> nat, gm). 
              (\<lambda>x y. fst x < fst y \<or> fst x = fst y \<and> snd x < snd y)\<inverse>\<inverse> fn gm}"
  proof (fold lex_prodp_def pr_strict_def, rule wf_imp_SN)
    show "wf ({(fn, gm). pr_strict\<inverse>\<inverse> fn gm}\<inverse>)"
      using wfp_pr_strict
      by (simp add: wfp_pr_strict converse_def wfp_def)
  qed
qed (auto simp: order.order_iff_strict)

instantiation nat :: weighted begin

definition weights_nat :: "nat weights" where "weights_nat \<equiv> weights"

instance
  using weights_adm pr_strict_total pr_strict_asymp
  by (intro_classes, unfold weights_nat_def) auto

end

instantiation nat :: infinite begin

instance
  by intro_classes simp

end

fun repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "repeat 0 _ = []"
| "repeat (Suc n) x = x # repeat n x"

abbreviation types :: "nat \<Rightarrow> type list \<times> type" where
  "types n \<equiv>
    let type = if even n then A else B
    in (repeat (n div 2) type, type)"

lemma types_inhabited: "\<exists>f. types f = ([], \<tau>)"
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

sublocale wellfounded_strict_order "trivial_tiebreakers C\<^sub>G"
  using trivial_tiebreakers.

sublocale nonground_term_with_context .

sublocale nonground_equality_order less_kbo
  by unfold_locales

sublocale
  superposition_calculus
    "select_max :: (nat, nat) select"
    less_kbo
    types
    trivial_tiebreakers
proof unfold_locales
  fix \<tau>
  show "\<exists>f. types f = ([], \<tau>)"
    using types_inhabited .
next
  show "|UNIV :: type set| \<le>o |UNIV :: nat set|"
    using UNIV_type_ordLeq_UNIV_nat .
qed

end

end
