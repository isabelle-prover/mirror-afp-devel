(* License: LGPL *)

subsection \<open>Components of Expressiveness Prices\<close>

theory Expressiveness_Price
  imports HML_SRBB Energy
begin

text \<open>The (maximal) modal depth (of observations $\langle\alpha\rangle$, $(\alpha)$) is increased on each \<^term>\<open>Obs\<close> and \<^term>\<open>BranchConj\<close>.\<close>

primrec
      modal_depth_srbb :: \<open>('act, 'i) hml_srbb \<Rightarrow> enat\<close>
  and modal_depth_srbb_inner :: \<open>('act, 'i) hml_srbb_inner \<Rightarrow> enat\<close>
  and modal_depth_srbb_conjunct :: \<open>('act, 'i) hml_srbb_conjunct \<Rightarrow> enat\<close> where
 \<open>modal_depth_srbb TT = 0\<close> |
 \<open>modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_inner \<chi>\<close> |
 \<open>modal_depth_srbb (ImmConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close> |

 \<open>modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>\<close> |
 \<open>modal_depth_srbb_inner (Conj I \<psi>s) =
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close> |
 \<open>modal_depth_srbb_inner (StableConj I \<psi>s) =
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close> |
 \<open>modal_depth_srbb_inner (BranchConj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))\<close> |

 \<open>modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>\<close> |
 \<open>modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>\<close>

text \<open>The depth of branching conjunctions (with one observation clause not starting with $\langle\varepsilon\rangle$) is increased on each: \<^term>\<open>BranchConj\<close>.\<close>

primrec
      branching_conjunction_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and branch_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and branch_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>branching_conjunction_depth TT = 0\<close> |
  \<open>branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_inner \<chi>\<close> |
  \<open>branching_conjunction_depth (ImmConj I \<psi>s) =
    Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |

  \<open>branch_conj_depth_inner (Obs _ \<phi>) = branching_conjunction_depth \<phi>\<close> |
  \<open>branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>branch_conj_depth_inner (StableConj I \<psi>s) =
    Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>branch_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
     1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>branch_conj_depth_conjunct (Pos \<chi>) = branch_conj_depth_inner \<chi>\<close> |
  \<open>branch_conj_depth_conjunct (Neg \<chi>) = branch_conj_depth_inner \<chi>\<close>

text \<open>The depth of stable conjunctions (that do enforce stability by a $\neg\langle\tau\rangle\top$-conjunct) is increased on each \<^term>\<open>StableConj\<close>. Note that if the \<open>StableConj\<close> is empty (has no other conjuncts), it is still counted.\<close>

primrec
      stable_conjunction_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and st_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and st_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>stable_conjunction_depth TT = 0\<close> |
  \<open>stable_conjunction_depth (Internal \<chi>) = st_conj_depth_inner \<chi>\<close> |
  \<open>stable_conjunction_depth (ImmConj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |

  \<open>st_conj_depth_inner (Obs _ \<phi>) = stable_conjunction_depth \<phi>\<close> |
  \<open>st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>st_conj_depth_inner (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>st_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>st_conj_depth_conjunct (Pos \<chi>) = st_conj_depth_inner \<chi>\<close> |
  \<open>st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>\<close>

text \<open>
  The depth of unstable conjunctions (that do not enforce stability by a $\neg\langle\tau\rangle\top$-conjunct) is increased on each:

   \<^item> \<^term>\<open>ImmConj\<close> if there are conjuncts (i.e. $\bigwedge\{\}$ is not counted)
   \<^item> \<^term>\<open>Conj\<close> if there are conjuncts, (i.e. the conjunction is not empty)
   \<^item> \<^term>\<open>BranchConj\<close>.
\<close>

primrec
      unstable_conjunction_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and inst_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and inst_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>unstable_conjunction_depth TT = 0\<close> |
  \<open>unstable_conjunction_depth (Internal \<chi>) = inst_conj_depth_inner \<chi>\<close> |
  \<open>unstable_conjunction_depth (ImmConj I \<psi>s) =
    (if I = {}
     then 0
     else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>inst_conj_depth_inner (Obs _ \<phi>) = unstable_conjunction_depth \<phi>\<close> |
  \<open>inst_conj_depth_inner (Conj I \<psi>s) =
    (if I = {}
     then 0
     else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |
  \<open>inst_conj_depth_inner (StableConj I \<psi>s) =
    Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>inst_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    1 + Sup ({unstable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>inst_conj_depth_conjunct (Pos \<chi>) = inst_conj_depth_inner \<chi>\<close> |
  \<open>inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>\<close>

text \<open>The depth of immediate conjunctions (that are not preceded by $\langle\varepsilon\rangle$)
is increased on each \<^term>\<open>ImmConj\<close> if there are conjuncts (i.e. $\bigwedge\{\}$ is not counted).\<close>

primrec
      immediate_conjunction_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and imm_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and imm_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>immediate_conjunction_depth TT = 0\<close> |
  \<open>immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_inner \<chi>\<close> |
  \<open>immediate_conjunction_depth (ImmConj I \<psi>s) =
    (if I = {}
     then 0
     else 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>imm_conj_depth_inner (Obs _ \<phi>) = immediate_conjunction_depth \<phi>\<close> |
  \<open>imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>imm_conj_depth_inner (StableConj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>imm_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>imm_conj_depth_conjunct (Pos \<chi>) = imm_conj_depth_inner \<chi>\<close> |
  \<open>imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>\<close>

text \<open>The maximal modal depth of positive clauses in conjunctions calculates the modal depth for every positive clause in a conjunction (\<^term>\<open>Pos \<chi>\<close>).\<close>

primrec
      max_positive_conjunct_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and max_pos_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and max_pos_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>max_positive_conjunct_depth TT = 0\<close> |
  \<open>max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_inner \<chi>\<close> |
  \<open>max_positive_conjunct_depth (ImmConj I \<psi>s) =
    Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |

  \<open>max_pos_conj_depth_inner (Obs _ \<phi>) = max_positive_conjunct_depth \<phi>\<close> |
  \<open>max_pos_conj_depth_inner (Conj I \<psi>s) =
    Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>max_pos_conj_depth_inner (StableConj I \<psi>s) =
    Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>max_pos_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>, max_positive_conjunct_depth \<phi>}
        \<union> ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>max_pos_conj_depth_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>\<close> |
  \<open>max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>\<close>

text \<open>The maximal modal depth of negative clauses in conjunctions calculates the modal depth for every negative clause in a conjunction (\<^term>\<open>Neg \<chi>\<close>).\<close>

primrec
      max_negative_conjunct_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and max_neg_conj_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and max_neg_conj_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>max_negative_conjunct_depth TT = 0\<close> |
  \<open>max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_inner \<chi>\<close> |
  \<open>max_negative_conjunct_depth (ImmConj I \<psi>s) =
    Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |

  \<open>max_neg_conj_depth_inner (Obs _ \<phi>) = max_negative_conjunct_depth \<phi>\<close> |
  \<open>max_neg_conj_depth_inner (Conj I \<psi>s) =
    Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>max_neg_conj_depth_inner (StableConj I \<psi>s) =
    Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>max_neg_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>max_neg_conj_depth_conjunct (Pos \<chi>) = max_neg_conj_depth_inner \<chi>\<close> |
  \<open>max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>\<close>

text \<open>The depth of negations on a path of the syntax tree) is increased on each \<^term>\<open>Neg \<chi>\<close>.\<close>

primrec
      negation_depth :: \<open>('a, 's) hml_srbb \<Rightarrow> enat\<close>
  and neg_depth_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> enat\<close>
  and neg_depth_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> enat\<close> where
  \<open>negation_depth TT = 0\<close> |
  \<open>negation_depth (Internal \<chi>) = neg_depth_inner \<chi>\<close> |
  \<open>negation_depth (ImmConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close> |

  \<open>neg_depth_inner (Obs _ \<phi>) = negation_depth \<phi>\<close> |
  \<open>neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>neg_depth_inner (StableConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close> |
  \<open>neg_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    Sup ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<psi>s) ` I))\<close> |

  \<open>neg_depth_conjunct (Pos \<chi>) = neg_depth_inner \<chi>\<close> |
  \<open>neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>\<close>

subsection \<open>Properties of Price Components\<close>

lemma \<open>modal_depth_srbb TT = 0\<close>
  using Sup_enat_def by simp

lemma \<open>modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> TT {} \<psi>s2)))) = 2\<close>
  using Sup_enat_def by simp

fun observe_n_alphas :: \<open>'a \<Rightarrow> nat \<Rightarrow> ('a, nat) hml_srbb\<close> where
  \<open>observe_n_alphas \<alpha> 0 = TT\<close> |
  \<open>observe_n_alphas \<alpha> (Suc n) = Internal (Obs \<alpha> (observe_n_alphas \<alpha> n))\<close>

lemma obs_n_\<alpha>_depth_n: \<open>modal_depth_srbb (observe_n_alphas \<alpha> n) = n\<close>
proof (induct n)
  case 0
  show ?case unfolding observe_n_alphas.simps(1) and modal_depth_srbb.simps(2)
    using zero_enat_def and Sup_enat_def by force
next
  case (Suc n)
  then show ?case
    using eSuc_enat plus_1_eSuc(1) by auto
qed

lemma sup_nats_in_enats_infinite: \<open>(SUP x\<in>\<nat>. enat x) = \<infinity>\<close>
  by (metis Nats_infinite Sup_enat_def enat.inject finite.emptyI finite_imageD inj_on_def)

lemma sucs_of_nats_in_enats_sup_infinite: \<open>(SUP x\<in>\<nat>. 1 + enat x) = \<infinity>\<close>
  using sup_nats_in_enats_infinite
  by (metis Sup.SUP_cong eSuc_Sup eSuc_infinity image_image image_is_empty plus_1_eSuc(1))

lemma \<open>modal_depth_srbb (ImmConj \<nat> (\<lambda>n. Pos (Obs \<alpha> (observe_n_alphas \<alpha> n)))) = \<infinity>\<close>
  unfolding modal_depth_srbb.simps(3)
        and o_def
        and modal_depth_srbb_conjunct.simps(1)
        and modal_depth_srbb_inner.simps(1)
        and obs_n_\<alpha>_depth_n
  by (metis sucs_of_nats_in_enats_sup_infinite)

lemma modal_depth_dominates_pos_conjuncts:
  fixes
    \<phi>::\<open>('a, 's) hml_srbb\<close> and
    \<chi>::\<open>('a, 's) hml_srbb_inner\<close> and
    \<psi>::\<open>('a, 's) hml_srbb_conjunct\<close>
  shows
    \<open>(max_positive_conjunct_depth \<phi> \<le> modal_depth_srbb \<phi>)
    \<and> (max_pos_conj_depth_inner \<chi> \<le> modal_depth_srbb_inner \<chi>)
    \<and> (max_pos_conj_depth_conjunct \<psi> \<le> modal_depth_srbb_conjunct \<psi>)\<close>
  using hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct[of
        \<open>\<lambda>\<phi>::('a, 's) hml_srbb. max_positive_conjunct_depth \<phi> \<le> modal_depth_srbb \<phi>\<close>
        \<open>\<lambda>\<chi>. max_pos_conj_depth_inner \<chi> \<le> modal_depth_srbb_inner \<chi>\<close>
        \<open>\<lambda>\<psi>. max_pos_conj_depth_conjunct \<psi> \<le> modal_depth_srbb_conjunct \<psi>\<close>]
  by (auto simp add: SUP_mono' add_increasing sup.coboundedI1 sup.coboundedI2)

lemma modal_depth_dominates_neg_conjuncts:
  fixes
    \<phi>::\<open>('a, 's) hml_srbb\<close> and
    \<chi>::\<open>('a, 's) hml_srbb_inner\<close> and
    \<psi>::\<open>('a, 's) hml_srbb_conjunct\<close>
  shows
    \<open>(max_negative_conjunct_depth \<phi> \<le> modal_depth_srbb \<phi>)
    \<and> (max_neg_conj_depth_inner \<chi> \<le> modal_depth_srbb_inner \<chi>)
    \<and> (max_neg_conj_depth_conjunct \<psi> \<le> modal_depth_srbb_conjunct \<psi>)\<close>
  using hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct[of
        \<open>\<lambda>\<phi>::('a, 's) hml_srbb. max_negative_conjunct_depth \<phi> \<le> modal_depth_srbb \<phi>\<close>
        \<open>\<lambda>\<chi>. max_neg_conj_depth_inner \<chi> \<le> modal_depth_srbb_inner \<chi>\<close>
        \<open>\<lambda>\<psi>. max_neg_conj_depth_conjunct \<psi> \<le> modal_depth_srbb_conjunct \<psi>\<close>]
  by (auto simp add: SUP_mono' add_increasing sup.coboundedI1 sup.coboundedI2)

subsection \<open>Expressiveness Price Function\<close>

text \<open>The \<open>expressiveness_price\<close> function combines the eight component functions into one.\<close>

fun expressiveness_price :: \<open>('a, 's) hml_srbb \<Rightarrow> energy\<close> where
  \<open>expressiveness_price \<phi> =
    E (modal_depth_srbb            \<phi>)
      (branching_conjunction_depth \<phi>)
      (unstable_conjunction_depth  \<phi>)
      (stable_conjunction_depth    \<phi>)
      (immediate_conjunction_depth \<phi>)
      (max_positive_conjunct_depth \<phi>)
      (max_negative_conjunct_depth \<phi>)
      (negation_depth              \<phi>)\<close>

text \<open>Here, we can see the decomposed price of an immediate conjunction:\<close>
lemma expressiveness_price_ImmConj_def:
  shows \<open>expressiveness_price (ImmConj I \<psi>s) = E
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (if I = {} then 0 else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (if I = {} then 0 else 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))\<close> by simp

lemma expressiveness_price_ImmConj_non_empty_def:
  assumes \<open>I \<noteq> {}\<close>
  shows \<open>expressiveness_price (ImmConj I \<psi>s) = E
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))\<close> using assms  by simp

lemma expressiveness_price_ImmConj_empty_def:
  assumes \<open>I = {}\<close>
  shows \<open>expressiveness_price (ImmConj I \<psi>s) = E 0 0 0 0 0 0 0 0\<close> using assms
  unfolding expressiveness_price_ImmConj_def by (simp add: bot_enat_def)

text \<open>Formalizing HML$_\text{SRBB}$ by mutually recursive data types leads to expressiveness price functions of these other types and corresponding definitions and lemmas.\<close>

fun expr_pr_inner :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> energy\<close> where
  \<open>expr_pr_inner \<chi> =
    E (modal_depth_srbb_inner \<chi>)
      (branch_conj_depth_inner \<chi>)
      (inst_conj_depth_inner \<chi>)
      (st_conj_depth_inner \<chi>)
      (imm_conj_depth_inner \<chi>)
      (max_pos_conj_depth_inner \<chi>)
      (max_neg_conj_depth_inner \<chi>)
      (neg_depth_inner \<chi>)\<close>

fun expr_pr_conjunct :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> energy\<close> where
  \<open>expr_pr_conjunct \<psi> =
    E (modal_depth_srbb_conjunct \<psi>)
      (branch_conj_depth_conjunct \<psi>)
      (inst_conj_depth_conjunct \<psi>)
      (st_conj_depth_conjunct \<psi>)
      (imm_conj_depth_conjunct \<psi>)
      (max_pos_conj_depth_conjunct \<psi>)
      (max_neg_conj_depth_conjunct \<psi>)
      (neg_depth_conjunct \<psi>)\<close>

subsection \<open>Prices of Certain Formulas\<close>

context lts_tau
begin

text \<open>For example, here, we establish that the expressiveness price of \<open>Internal \<chi>\<close> is equal to the expressiveness price of \<open>\<chi>\<close>.\<close>

lemma expr_internal_eq:
  shows \<open>expressiveness_price (Internal \<chi>) = expr_pr_inner \<chi>\<close>
  by auto

lemma expr_pos:
  assumes \<open>expr_pr_inner \<chi> \<le> the (min1_6 e)\<close>
  shows \<open>expr_pr_conjunct (Pos \<chi>) \<le> e\<close>
  using assms by auto

lemma expr_neg:
  assumes
    \<open>expr_pr_inner \<chi> \<le> e'\<close>
    \<open>(Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) = Some e'\<close>
  shows \<open>expr_pr_conjunct (Neg \<chi>) \<le> e\<close>
proof -
  have expr_neg: \<open>expr_pr_conjunct (Neg \<chi>) =
    E (modal_depth_srbb_conjunct (Neg \<chi>))
      (branch_conj_depth_conjunct (Neg \<chi>))
      (inst_conj_depth_conjunct (Neg \<chi>))
      (st_conj_depth_conjunct (Neg \<chi>))
      (imm_conj_depth_conjunct (Neg \<chi>))
      (max_pos_conj_depth_conjunct (Neg \<chi>))
      (max_neg_conj_depth_conjunct (Neg \<chi>))
      (neg_depth_conjunct (Neg \<chi>))\<close>
    using expr_pr_conjunct.simps by blast
  have neg_ups:
    \<open>modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>\<close>
    \<open>(branch_conj_depth_conjunct (Neg \<chi>)) = branch_conj_depth_inner \<chi>\<close>
    \<open>inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>\<close>
    \<open>st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>\<close>
    \<open>imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>\<close>
    \<open>max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>\<close>
    \<open>max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>\<close>
    \<open>neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>\<close>
    by simp+
  obtain e1 e2 e3 e4 e5 e6 e7 e8 where e_def: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
    by (metis energy.exhaust_sel)
  hence is_some: \<open>(subtract_fn 0 0 0 0 0 0 0 1 e = Some (E e1 e2 e3 e4 e5 e6 e7 (e8-1)))\<close>
    using assms bind_eq_None_conv by fastforce
  hence \<open>modal_depth_srbb_inner \<chi> \<le> (min e1 e7)\<close>
    using assms expr_pr_inner.simps leq_components min_1_7_subtr_simp e_def
    by (metis energy.sel(1) energy.sel(7) option.discI option.inject)
  moreover have \<open>neg_depth_inner \<chi> \<le> (e8-1)\<close>
    using e_def is_some energy_minus leq_components min_1_7_simps assms
    by (smt (verit, ccfv_threshold) bind.bind_lunit energy.sel(8) expr_pr_inner.simps option.sel)
  moreover hence \<open>neg_depth_conjunct (Neg \<chi>) \<le> e8\<close>
    using \<open>neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>\<close>
    by (metis is_some add_diff_assoc_enat add_diff_cancel_enat e_def enat.simps(3)
        enat_defs(2) enat_diff_mono energy.sel(8) leq_components linorder_not_less
        option.distinct(1) order_le_less)
  ultimately show \<open>expr_pr_conjunct (Neg \<chi>) \<le> e\<close>
    using expr_neg e_def is_some assms neg_ups assms leq_components min_1_7_subtr_simp
    by (metis energy.sel expr_pr_inner.simps min.bounded_iff option.distinct(1) option.inject)
qed

lemma expr_obs:
  assumes
    \<open>expressiveness_price \<phi> \<le> e'\<close>
    \<open>subtract_fn 1 0 0 0 0 0 0 0 e = Some e'\<close>
  shows \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<le> e\<close>
  using assms
  by (simp) (metis add_diff_cancel_enat add_mono_thms_linordered_semiring(1)
      enat.simps(3) enat_defs(2) energy.sel idiff_0_right
      le_iff_add le_numeral_extra(4) minus_energy_def option.discI
      option.inject)

lemma expr_st_conj:
  assumes
    \<open>subtract_fn  0 0 0 1 0 0 0 0 e = Some e'\<close>
    \<open>I \<noteq> {}\<close>
    \<open>\<forall>q \<in> I. expr_pr_conjunct (\<psi>s q) \<le> e'\<close>
  shows
    \<open>expr_pr_inner (StableConj I \<psi>s) \<le> e\<close>
proof -
  have st_conj_upds:
    \<open>modal_depth_srbb_inner (StableConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>branch_conj_depth_inner (StableConj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>inst_conj_depth_inner (StableConj I \<psi>s) = Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>st_conj_depth_inner (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>imm_conj_depth_inner (StableConj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>max_pos_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>max_neg_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>neg_depth_inner (StableConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    by force+
  obtain e1 e2 e3 e4 e5 e6 e7 e8 where e_def: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
    using energy.exhaust_sel by blast
  hence is_some: \<open>subtract_fn  0 0 0 1 0 0 0 0 e = Some (E e1 e2 e3 (e4-1) e5 e6 e7 e8)\<close>
    using assms minus_energy_def
    by (smt (verit, del_insts) energy_minus idiff_0_right option.distinct(1))
  hence
    \<open>\<forall>i \<in> I. modal_depth_srbb_conjunct (\<psi>s i) \<le> e1\<close>
    \<open>\<forall>i \<in> I. branch_conj_depth_conjunct (\<psi>s i) \<le> e2\<close>
    \<open>\<forall>i \<in> I. inst_conj_depth_conjunct (\<psi>s i) \<le> e3\<close>
    \<open>\<forall>i \<in> I. st_conj_depth_conjunct (\<psi>s i) \<le> (e4 - 1)\<close>
    \<open>\<forall>i \<in> I. imm_conj_depth_conjunct (\<psi>s i) \<le> e5\<close>
    \<open>\<forall>i \<in> I. max_pos_conj_depth_conjunct (\<psi>s i) \<le> e6\<close>
    \<open>\<forall>i \<in> I. max_neg_conj_depth_conjunct (\<psi>s i) \<le> e7\<close>
    \<open>\<forall>i \<in> I. neg_depth_conjunct (\<psi>s i) \<le> e8\<close>
    using assms unfolding leq_components by auto
  hence sups:
    \<open>Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1\<close>
    \<open>Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2\<close>
    \<open>Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e3\<close>
    \<open>Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e4 - 1)\<close>
    \<open>Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e5\<close>
    \<open>Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6\<close>
    \<open>Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7\<close>
    \<open>Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8\<close>
    by (simp add: Sup_le_iff)+
  hence \<open>st_conj_depth_inner (StableConj I \<psi>s) \<le> e4\<close>
    using e_def is_some minus_energy_def leq_components st_conj_upds(4)
    by (metis add_diff_cancel_enat add_left_mono enat.simps(3) enat_defs(2) energy.sel(4)
        le_iff_add option.distinct(1))
  then show ?thesis
    using st_conj_upds sups
    by (simp add: e_def)
qed

lemma expr_imm_conj:
  assumes
    \<open>subtract_fn  0 0 0 0 1 0 0 0 e = Some e'\<close>
    \<open>I \<noteq> {}\<close>
    \<open>expr_pr_inner (Conj I \<psi>s) \<le> e'\<close>
  shows \<open>expressiveness_price (ImmConj I \<psi>s) \<le> e\<close>
proof -
  have conj_upds:
    \<open>modal_depth_srbb_inner (Conj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>inst_conj_depth_inner (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>max_pos_conj_depth_inner (Conj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>max_neg_conj_depth_inner (Conj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    using assms
    by force+
  have imm_conj_upds:
    \<open>modal_depth_srbb (ImmConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>branching_conjunction_depth (ImmConj I \<psi>s) = Sup ((branch_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>unstable_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>stable_conjunction_depth (ImmConj I \<psi>s) = Sup ((st_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>immediate_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((imm_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>max_positive_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>max_negative_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    \<open>negation_depth (ImmConj I \<psi>s) = Sup ((neg_depth_conjunct\<circ>\<psi>s) ` I)\<close>
    using assms
    by force+
  obtain e1 e2 e3 e4 e5 e6 e7 e8 where e_def: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
    using assms by (metis energy.exhaust_sel)
  hence is_some: \<open>(e - (E 0 0 0 0 1 0 0 0)) = (E e1 e2 e3 e4 (e5-1) e6 e7 e8)\<close>
    using minus_energy_def
    by simp
  hence \<open>e5>0\<close> using assms(1) e_def leq_components by auto
  have
    \<open>E (modal_depth_srbb_inner (Conj I \<psi>s))
       (branch_conj_depth_inner (Conj I \<psi>s))
       (inst_conj_depth_inner (Conj I \<psi>s))
       (st_conj_depth_inner (Conj I \<psi>s))
       (imm_conj_depth_inner (Conj I \<psi>s))
       (max_pos_conj_depth_inner (Conj I \<psi>s))
       (max_neg_conj_depth_inner (Conj I \<psi>s))
       (neg_depth_inner (Conj I \<psi>s)) \<le> (E e1 e2 e3 e4 (e5-1) e6 e7 e8)\<close>
    using is_some assms
    by (metis expr_pr_inner.simps option.discI option.inject)
  hence
    \<open>(modal_depth_srbb_inner (Conj I \<psi>s))\<le> e1\<close>
    \<open>(branch_conj_depth_inner (Conj I \<psi>s)) \<le> e2\<close>
    \<open>(inst_conj_depth_inner (Conj I \<psi>s)) \<le> e3\<close>
    \<open>(st_conj_depth_inner (Conj I \<psi>s))\<le> e4\<close>
    \<open>(imm_conj_depth_inner (Conj I \<psi>s))\<le> (e5-1)\<close>
    \<open>(max_pos_conj_depth_inner (Conj I \<psi>s)) \<le> e6\<close>
    \<open>(max_neg_conj_depth_inner (Conj I \<psi>s)) \<le> e7\<close>
    \<open>(neg_depth_inner (Conj I \<psi>s))\<le> e8\<close>
    by auto
  hence E:
    \<open>Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1\<close>
    \<open>Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2\<close>
    \<open>1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e3\<close>
    \<open>Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e4\<close>
    \<open>Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e5-1)\<close>
    \<open>Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6\<close>
    \<open>Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7\<close>
    \<open>Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8\<close>
    using conj_upds by force+
  from this(5) have \<open>(1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)) \<le> e5\<close>
    using assms(1) \<open>e5>0\<close> is_some e_def add.right_neutral
      add_diff_cancel_enat enat_add_left_cancel_le ileI1 le_iff_add plus_1_eSuc(1)
    by metis
  thus \<open>expressiveness_price (ImmConj I \<psi>s) \<le> e\<close> using imm_conj_upds E
    by (metis e_def  energy.sel expressiveness_price.elims leD somewhere_larger_eq)
qed

lemma expr_conj:
  assumes
    \<open>subtract_fn 0 0 1 0 0 0 0 0 e = Some e'\<close>
    \<open>I \<noteq> {}\<close>
    \<open>\<forall>q \<in> I. expr_pr_conjunct (\<psi>s q) \<le> e'\<close>
  shows \<open>expr_pr_inner (Conj I \<psi>s) \<le> e\<close>
proof -
  have conj_upds:
    \<open>modal_depth_srbb_inner (Conj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>inst_conj_depth_inner (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>max_pos_conj_depth_inner (Conj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>max_neg_conj_depth_inner (Conj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    \<open>neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    using assms by force+
  obtain e1 e2 e3 e4 e5 e6 e7 e8 where e_def: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
    using energy.exhaust_sel by metis
  hence is_some: \<open>e - (E 0 0 1 0 0 0 0 0) = E e1 e2 (e3-1) e4 e5 e6 e7 e8\<close>
    using minus_energy_def by simp
  hence \<open>e3>0\<close> using assms(1) e_def leq_components by auto
  hence
    \<open>\<forall>i \<in> I. modal_depth_srbb_conjunct (\<psi>s i) \<le> e1\<close>
    \<open>\<forall>i \<in> I. branch_conj_depth_conjunct (\<psi>s i) \<le> e2\<close>
    \<open>\<forall>i \<in> I. inst_conj_depth_conjunct (\<psi>s i) \<le> (e3-1)\<close>
    \<open>\<forall>i \<in> I. st_conj_depth_conjunct (\<psi>s i) \<le> e4\<close>
    \<open>\<forall>i \<in> I. imm_conj_depth_conjunct (\<psi>s i) \<le> e5\<close>
    \<open>\<forall>i \<in> I. max_pos_conj_depth_conjunct (\<psi>s i) \<le> e6\<close>
    \<open>\<forall>i \<in> I. max_neg_conj_depth_conjunct (\<psi>s i) \<le> e7\<close>
    \<open>\<forall>i \<in> I. neg_depth_conjunct (\<psi>s i) \<le> e8\<close>
    using assms is_some energy.sel leq_components
    by (metis expr_pr_conjunct.elims option.distinct(1) option.inject)+
  hence sups:
    \<open>Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1\<close>
    \<open>Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2\<close>
    \<open>Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e3-1)\<close>
    \<open>Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e4\<close>
    \<open>Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e5\<close>
    \<open>Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6\<close>
    \<open>Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7\<close>
    \<open>Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8\<close>
    by (simp add: Sup_le_iff)+
  hence \<open>inst_conj_depth_inner (Conj I \<psi>s) \<le> e3\<close>
    using \<open>e3>0\<close> is_some e_def
    unfolding conj_upds(3)
    by (metis add.right_neutral add_diff_cancel_enat enat_add_left_cancel_le ileI1
        le_iff_add plus_1_eSuc(1))
  then show ?thesis
    using conj_upds sups
    by (simp add: e_def)
qed

lemma expr_br_conj:
  assumes
    \<open>subtract_fn 0 1 1 0 0 0 0 0 e = Some e'\<close>
    \<open>min1_6 e' = Some e''\<close>
    \<open>subtract_fn 1 0 0 0 0 0 0 0 e'' = Some e'''\<close>
    \<open>expressiveness_price \<phi> \<le> e'''\<close>
    \<open>\<forall>q \<in> Q. expr_pr_conjunct (\<Phi> q) \<le> e'\<close>
    \<open>1 + modal_depth_srbb \<phi> \<le> pos_conjuncts e\<close>
  shows \<open>expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e\<close>
proof -
  obtain e1 e2 e3 e4 e5 e6 e7 e8 where e_def: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
    by (smt (z3) energy.exhaust)
  hence e'''_def: \<open>e''' = (E ((min e1 e6)-1) (e2-1) (e3-1) e4 e5 e6 e7 e8)\<close>
    using minus_energy_def
    by (smt (z3) assms energy.sel idiff_0_right min_1_6_simps option.distinct(1) option.sel)
  hence min_vals: \<open>the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)
      = (E ((min e1 e6)-1) (e2-1) (e3-1) e4 e5 e6 e7 e8)\<close>
    using assms
    by (metis not_Some_eq option.sel)
  hence \<open>0 < e1\<close> \<open>0 < e2\<close> \<open>0 < e3\<close> \<open>0 < e6\<close>
    using assms energy.sel min_1_6_simps
    unfolding e_def minus_energy_def leq_components
    by (metis (no_types, lifting) gr_zeroI idiff_0_right min_enat_simps(3)
        not_one_le_zero option.distinct(1) option.sel, auto)
  have e_comp: \<open>e - (E 0 1 1 0 0 0 0 0) = E e1 (e2-1) (e3-1) e4 e5 e6 e7 e8\<close> using e_def
    by simp
  have conj:
    \<open>E (modal_depth_srbb            \<phi>)
       (branching_conjunction_depth \<phi>)
       (unstable_conjunction_depth  \<phi>)
       (stable_conjunction_depth    \<phi>)
       (immediate_conjunction_depth \<phi>)
       (max_positive_conjunct_depth \<phi>)
       (max_negative_conjunct_depth \<phi>)
       (negation_depth              \<phi>)
          \<le> ((E ((min e1 e6)-1) (e2-1) (e3-1) e4 e5 e6 e7 e8))\<close>
    using assms e'''_def by force
  hence conj_single:
    \<open>modal_depth_srbb \<phi>              \<le> ((min e1 e6)-1)\<close>
    \<open>branching_conjunction_depth  \<phi>  \<le> e2 -1\<close>
    \<open>(unstable_conjunction_depth  \<phi>) \<le> e3-1\<close>
    \<open>(stable_conjunction_depth    \<phi>) \<le> e4\<close>
    \<open>(immediate_conjunction_depth \<phi>) \<le> e5\<close>
    \<open>(max_positive_conjunct_depth \<phi>) \<le> e6\<close>
    \<open>(max_negative_conjunct_depth \<phi>) \<le> e7\<close>
    \<open>(negation_depth              \<phi>) \<le> e8\<close>
    using leq_components by auto
  have \<open>0 < (min e1 e6)\<close> using \<open>0 < e1\<close> \<open>0 < e6\<close>
    using min_less_iff_conj by blast
  hence \<open>1 + modal_depth_srbb \<phi> \<le> (min e1 e6)\<close>
    using conj_single add.commute add_diff_assoc_enat add_diff_cancel_enat
      add_right_mono conj_single(2) i1_ne_infinity ileI1 one_eSuc
    by (metis (no_types, lifting))
  hence \<open>1 + modal_depth_srbb \<phi> \<le> e1\<close> \<open>1 + modal_depth_srbb \<phi> \<le> e6\<close>
    using min.bounded_iff by blast+
  from conj have \<open>1 + branching_conjunction_depth \<phi> \<le> e2\<close>
    by (metis \<open>0 < e2\<close> add.commute add_diff_assoc_enat add_diff_cancel_enat
        add_right_mono conj_single(2) i1_ne_infinity ileI1 one_eSuc)
  from conj_single have \<open>1 + unstable_conjunction_depth \<phi> \<le> e3\<close>
    using \<open>0 < e3\<close> add.commute add_diff_assoc_enat add_diff_cancel_enat
      add_right_mono conj_single(2) i1_ne_infinity ileI1 one_eSuc
    by (metis (no_types, lifting))
  have branch: \<open>\<forall>q\<in>Q.
    E (modal_depth_srbb_conjunct (\<Phi> q))
      (branch_conj_depth_conjunct  (\<Phi> q))
      (inst_conj_depth_conjunct  (\<Phi> q))
      (st_conj_depth_conjunct  (\<Phi> q))
      (imm_conj_depth_conjunct  (\<Phi> q))
      (max_pos_conj_depth_conjunct  (\<Phi> q))
      (max_neg_conj_depth_conjunct  (\<Phi> q))
      (neg_depth_conjunct  (\<Phi> q))
    \<le> (E e1 (e2-1) (e3-1) e4 e5 e6 e7 e8)\<close>
    using assms e_def e_comp
    by (metis expr_pr_conjunct.simps option.distinct(1) option.sel)
  hence branch_single:
    \<open>\<forall>q\<in>Q. (modal_depth_srbb_conjunct (\<Phi> q)) \<le> e1\<close>
    \<open>\<forall>q\<in>Q. (branch_conj_depth_conjunct  (\<Phi> q)) \<le> (e2-1)\<close>
    \<open>\<forall>q\<in>Q. (inst_conj_depth_conjunct  (\<Phi> q)) \<le> (e3-1)\<close>
    \<open>\<forall>q\<in>Q. (st_conj_depth_conjunct  (\<Phi> q)) \<le> e4\<close>
    \<open>\<forall>q\<in>Q. (imm_conj_depth_conjunct  (\<Phi> q)) \<le> e5\<close>
    \<open>\<forall>q\<in>Q. (max_pos_conj_depth_conjunct  (\<Phi> q)) \<le> e6\<close>
    \<open>\<forall>q\<in>Q. (max_neg_conj_depth_conjunct  (\<Phi> q)) \<le> e7\<close>
    \<open>\<forall>q\<in>Q. (neg_depth_conjunct  (\<Phi> q)) \<le> e8\<close>
    by auto
  hence \<open>\<forall>q\<in>Q. (1 + branch_conj_depth_conjunct  (\<Phi> q)) \<le> e2\<close>
    by (metis \<open>0 < e2\<close> add.commute add_diff_assoc_enat add_diff_cancel_enat
        add_right_mono i1_ne_infinity ileI1 one_eSuc)
  from branch_single have \<open>\<forall>q\<in>Q. (1 + inst_conj_depth_conjunct  (\<Phi> q)) \<le> e3\<close>
    using \<open>0 < e3\<close>
    by (metis add.commute add_diff_assoc_enat add_diff_cancel_enat add_right_mono
        i1_ne_infinity ileI1 one_eSuc)
  have
    \<open>expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>)
    = E (modal_depth_srbb_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (branch_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (inst_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (st_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (imm_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (max_pos_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (max_neg_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
      (neg_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))\<close> by simp
  hence expr:
    \<open>expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>)
    = E (Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)))
      (1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (1 + Sup ({unstable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (Sup ({1 + modal_depth_srbb \<phi>, max_positive_conjunct_depth \<phi>}
        \<union> ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)))
      (Sup ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<Phi>) ` Q)))\<close> by auto
  from branch_single \<open>1 + modal_depth_srbb \<phi> \<le> e1\<close>
    have \<open>\<forall>x \<in> ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)). x \<le> e1\<close>
    by fastforce
  hence e1_le:
      \<open>(Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q))) \<le> e1\<close>
    using Sup_least by blast
  have \<open>\<forall>x \<in> {branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q).
       x \<le> e2 - 1\<close>
    using branch_single conj_single comp_apply image_iff insertE by auto
  hence e2_le:
      \<open>1 + Sup ({branching_conjunction_depth \<phi>}
        \<union> ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)) \<le> e2\<close>
    using Sup_least
    by (metis Un_insert_left \<open>0 < e2\<close> add.commute eSuc_minus_1 enat_add_left_cancel_le
        ileI1 le_iff_add one_eSuc plus_1_eSuc(2) sup_bot_left)
  have \<open>\<forall>x \<in> ({unstable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q)).
      x \<le> e3-1\<close>
    using conj_single branch_single
    using comp_apply image_iff insertE by auto
  hence e3_le:
      \<open>1 + Sup ({unstable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q)) \<le> e3\<close>
    using Un_insert_left \<open>0<e3\<close>  add.commute eSuc_minus_1 enat_add_left_cancel_le ileI1
      le_iff_add one_eSuc plus_1_eSuc(2) sup_bot_left
    by (metis Sup_least)
  have fa:
    \<open>\<forall>x \<in> ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)). x \<le> e4\<close>
    \<open>\<forall>x \<in> ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)). x \<le> e5\<close>
    \<open>\<forall>x \<in> ({1 + modal_depth_srbb \<phi>, max_positive_conjunct_depth \<phi>}
            \<union> ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)). x \<le> e6\<close>
    \<open>\<forall>x \<in> ({max_negative_conjunct_depth \<phi>}
            \<union> ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)). x \<le> e7\<close>
    \<open>\<forall>x \<in> ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<Phi>) ` Q)). x \<le> e8\<close>
      using conj_single branch_single \<open>1 + modal_depth_srbb \<phi> \<le> e6\<close> by auto
  hence
    \<open>(Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q))) \<le> e4\<close>
    \<open>(Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q))) \<le> e5\<close>
    \<open>(Sup ({1 + modal_depth_srbb \<phi>, max_positive_conjunct_depth \<phi>}
          \<union> ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q))) \<le> e6\<close>
    \<open>(Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q))) \<le> e7\<close>
    \<open>(Sup ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<Phi>) ` Q))) \<le> e8\<close>
    using Sup_least
    by metis+
  thus \<open>expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e\<close>
    using expr e3_le e2_le e1_le e_def energy.sel leq_components by presburger
qed

lemma expressiveness_price_ImmConj_geq_parts:
  assumes \<open>i \<in> I\<close>
  shows \<open>expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 \<ge> expr_pr_conjunct (\<psi>s i)\<close>
proof -
  from assms have \<open>I \<noteq> {}\<close> by blast
  from expressiveness_price_ImmConj_non_empty_def[OF \<open>I \<noteq> {}\<close>]
  have \<open>expressiveness_price (ImmConj I \<psi>s) \<ge> E 0 0 1 0 1 0 0 0\<close>
    using energy_leq_cases by force
  hence
  \<open>expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 = E
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))\<close>
    unfolding expressiveness_price_ImmConj_non_empty_def[OF \<open>I \<noteq> {}\<close>]
    by simp
  also have \<open>... \<ge> expr_pr_conjunct (\<psi>s i)\<close>
    using assms \<open>I \<noteq> {}\<close> SUP_upper unfolding leq_components by fastforce
  finally show ?thesis .
qed

lemma expressiveness_price_ImmConj_geq_parts':
  assumes \<open>i \<in> I\<close>
  shows
    \<open>(expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0) - E 0 0 1 0 0 0 0 0
    \<ge> expr_pr_conjunct (\<psi>s i)\<close>
  using expressiveness_price_ImmConj_geq_parts[OF assms]
    less_eq_energy_def minus_energy_def
  by (smt (z3) energy.sel idiff_0_right)

text \<open>Here, we show the prices for some specific formulas.\<close>

lemma example_\<phi>_cp:
  fixes op a b::\<open>'a\<close> and left right::\<open>'s\<close>
  defines \<open>\<phi> \<equiv>
    (Internal
      (Obs op
        (Internal
          (Conj {left, right}
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined))))))\<close>
  shows
    \<open>modal_depth_srbb            \<phi> = 2\<close>
    \<open>branching_conjunction_depth \<phi> = 0\<close>
    \<open>unstable_conjunction_depth  \<phi> = 1\<close>
    \<open>stable_conjunction_depth    \<phi> = 0\<close>
    \<open>immediate_conjunction_depth \<phi> = 0\<close>
    \<open>max_positive_conjunct_depth \<phi> = 1\<close>
    \<open>max_negative_conjunct_depth \<phi> = 0\<close>
    \<open>negation_depth              \<phi> = 0\<close>
  unfolding \<phi>_def by simp+

lemma \<open>expressiveness_price (Internal
      (Obs op
        (Internal
          (Conj {left, right}
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined)))))) = E 2 0 1 0 0 1 0 0\<close>
  by simp

lemma \<open>expressiveness_price TT = E 0 0 0 0 0 0 0 0\<close>
  by simp

lemma \<open>expressiveness_price (ImmConj {} \<psi>s) = E 0 0 0 0 0 0 0 0\<close>
  by (simp add: Sup_enat_def)

lemma \<open>expressiveness_price (Internal (Conj {} \<psi>s)) = E 0 0 0 0 0 0 0 0\<close>
  by (simp add: Sup_enat_def)

lemma \<open>expressiveness_price (Internal (BranchConj \<alpha> TT {} \<psi>s)) = E 1 1 1 0 0 1 0 0\<close>
  by (simp add: Sup_enat_def)

lemma expr_obs_phi:
  \<open>subtract_fn 1 0 0 0 0 0 0 0 (expr_pr_inner (Obs \<alpha> \<phi>)) = Some (expressiveness_price \<phi>)\<close>
  by simp

end \<comment> \<open>pause \<open>lts_tau\<close> context\<close>

subsection \<open>Characterizing Equivalence by Energy Coordinates\<close>

text \<open>
  We can now define a sublanguage of Hennessy--Milner Logic \<open>\<O>\<close> by the set of formulas with prices below an energy coordinate.
\<close>
definition \<O> :: \<open>energy \<Rightarrow> (('a, 's) hml_srbb) set\<close> where
  \<open>\<O> energy \<equiv> {\<phi> . expressiveness_price \<phi> \<le> energy}\<close>

lemma \<O>_sup: \<open>UNIV = \<O> (E \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity>)\<close> unfolding \<O>_def by auto

lemma price_hierarchy_entails_modal_hierarchy:
  assumes \<open>e1 \<le> e2\<close>
  shows \<open>\<O> e1 \<subseteq> \<O> e2\<close>
  using assms unfolding \<O>_def by auto

definition \<O>_inner :: \<open>energy \<Rightarrow> (('a, 's) hml_srbb_inner) set\<close> where
  \<open>\<O>_inner energy \<equiv> {\<chi> . expr_pr_inner \<chi> \<le> energy}\<close>

definition \<O>_conjunct :: \<open>energy \<Rightarrow> (('a, 's) hml_srbb_conjunct) set\<close> where
  \<open>\<O>_conjunct energy \<equiv> {\<chi> . expr_pr_conjunct \<chi> \<le> energy}\<close>

context lts_tau
begin

text \<open>A state \<open>p\<close> pre-orders another state \<open>q\<close> with respect to some energy \<open>e\<close> if and only if \<open>p\<close> HML pre-orders \<open>q\<close> with respect to the HML sublanguage \<^term>\<open>\<O> e\<close>.\<close>
definition expr_preord :: \<open>'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<preceq> _ _\<close> 60) where
  \<open>(p \<preceq> e q) \<equiv> preordered (\<O> e) p q\<close>

text \<open>Conversely, \<open>p\<close> and \<open>q\<close> are equivalent with respect to \<open>e\<close> if and only if they are equivalent with respect to that HML sublanguage \<^term>\<open>\<O> e\<close>.\<close>
definition expr_equiv :: \<open>'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<sim> _ _\<close> 60) where
  \<open>(p \<sim> e q) \<equiv> equivalent (\<O> e) p q\<close>

lemma price_hierachy_preorder_dual:
  assumes
    \<open>e1 \<le> e2\<close>
    \<open>p \<preceq> e2 q\<close>
  shows
    \<open>p \<preceq> e1 q\<close>
  using assms price_hierarchy_entails_modal_hierarchy expr_preord_def by auto

subsection \<open>Relational Effects of Prices\<close>

text \<open>
  Certain properties of prices influence the preorder/equivalence relations that are characterized by price coordinates. (This will be important for some behavioral equivalences that we will prove to be characterized by specific prices.)
\<close>

lemma distinction_combination_eta:
  fixes p q
  defines
    \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and>  (\<nexists>\<phi>. \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> 0 0) \<and> distinguishes \<phi> p q')}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi> q''') p' q'''\<close>
  shows
    \<open>\<forall>q'\<in> Q\<alpha>. hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
      {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (conjunctify_distinctions \<Phi> p')))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''\<in>{q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q''') p' q'''\<close>
  proof clarify
    fix q' q'' q'''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
    thus \<open>hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p' q''') p' q'''\<close>
       using assms(3)  distinction_conjunctification by blast
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (Internal (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
          (conjunctify_distinctions \<Phi> p')))  p' q''\<close>
    using silent_reachable.refl unfolding Q\<alpha>_def by fastforce
  thus \<open>\<forall>q'\<in> Q\<alpha>.
     hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
        {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
        (conjunctify_distinctions \<Phi> p')))) p q'\<close>
    using assms(2) by (auto) (metis silent_reachable.refl)+
qed

lemma distinction_conjunctification_two_way_price:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
    \<open>\<forall>q\<in>I. \<Phi> q \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  shows
    \<open>\<forall>q\<in>I.
      (if distinguishes (\<Phi> q) p q
        then conjunctify_distinctions
        else conjunctify_distinctions_dual
      ) \<Phi> p q \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
proof
  fix q
  assume \<open>q \<in> I\<close>
  show
    \<open>(if distinguishes (\<Phi> q) p q
      then conjunctify_distinctions
      else conjunctify_distinctions_dual
    ) \<Phi> p q \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      unfolding conjunctify_distinctions_def conjunctify_distinctions_dual_def \<O>_def \<O>_conjunct_def
      by fastforce
  next
    case (ImmConj J \<Psi>)
    hence \<open>J = {}\<close>
      using assms \<open>q \<in> I\<close> unfolding \<O>_def
      by (simp, metis iadd_is_0 immediate_conjunction_depth.simps(3) zero_one_enat_neq(1))
    then show ?thesis
      using assms \<open>q \<in> I\<close> ImmConj by fastforce
  qed
qed

lemma distinction_combination_eta_two_way:
  fixes p q p' \<Phi>
  defines
    \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and>  (\<nexists>\<phi>. \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)
          \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p))}\<close> and
    \<open>\<Psi>\<alpha> \<equiv> \<lambda>q'''. (
        if distinguishes (\<Phi> q''') p' q'''
        then conjunctify_distinctions
        else conjunctify_distinctions_dual
      ) \<Phi> p' q'''\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
        \<longrightarrow> distinguishes (\<Phi> q''') p' q''' \<or> distinguishes (\<Phi> q''') q''' p'\<close>
  shows
    \<open>\<forall>q'\<in> Q\<alpha>. hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
      {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      \<Psi>\<alpha>))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''\<in>{q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
      hml_srbb_conj.distinguishes (\<Psi>\<alpha> q''') p' q'''\<close>
  proof clarify
    fix q' q'' q'''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
    thus \<open>hml_srbb_conj.distinguishes (\<Psi>\<alpha> q''') p' q''' \<close>
      using assms(4) \<Psi>\<alpha>_def distinction_conjunctification_two_way mem_Collect_eq
      by (smt (verit, best))
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''\<in>{q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
      hml_srbb_inner.distinguishes (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
        \<Psi>\<alpha>)  p' q'''\<close>
    using srbb_dist_conjunct_implies_dist_conjunction
    unfolding lts_semantics.distinguishes_def
    by (metis (no_types, lifting))
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''. (\<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q''') \<longrightarrow>
      hml_srbb_inner.distinguishes
        (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} \<Psi>\<alpha>)  p' q'''\<close>
    by blast
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> distinguishes
      (Internal  (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} \<Psi>\<alpha>)) p' q''\<close>
    by (meson distinguishes_def hml_srbb_inner.distinguishes_def
        hml_srbb_models.simps(2) silent_reachable.refl)
  thus \<open>\<forall>q'\<in> Q\<alpha>. hml_srbb_inner.distinguishes
      (Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} \<Psi>\<alpha>))) p q'\<close>
    using assms(3)
    by auto (metis silent_reachable.refl)+
qed

lemma distinction_conjunctification_price:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q\<close>
    \<open>\<forall>q\<in>I. \<Phi> q \<in> \<O> pr\<close>
    \<open>modal_depth pr \<le> pos_conjuncts pr\<close>
  shows
    \<open>\<forall>q\<in>I. ((conjunctify_distinctions \<Phi> p) q) \<in> \<O>_conjunct pr\<close>
proof
  fix q
  assume \<open>q \<in> I\<close>
  show \<open>conjunctify_distinctions \<Phi> p q \<in> \<O>_conjunct pr\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      unfolding conjunctify_distinctions_def \<O>_def \<O>_conjunct_def
      by fastforce
  next
    case (ImmConj J \<Psi>)
    hence \<open>\<exists>i. i\<in>J \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q\<close>
      using \<open>q \<in> I\<close> assms(1) by fastforce
    moreover have \<open>conjunctify_distinctions \<Phi> p q
        = \<Psi> (SOME i. i\<in>J \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q)\<close>
      unfolding ImmConj conjunctify_distinctions_def by simp
    ultimately have \<Psi>_i:
      \<open>\<exists>i\<in>J. hml_srbb_conj.distinguishes (\<Psi> i) p q \<and> conjunctify_distinctions \<Phi> p q = \<Psi> i\<close>
      by (metis (no_types, lifting) some_eq_ex)
    hence \<open>conjunctify_distinctions \<Phi> p q \<in> \<Psi>`J\<close>
      unfolding image_iff by blast
    hence
      \<open>expr_pr_conjunct (conjunctify_distinctions \<Phi> p q)
        \<le> expressiveness_price (ImmConj J \<Psi>)\<close>
      by (smt (verit, best) \<Psi>_i dual_order.trans expressiveness_price_ImmConj_geq_parts
          gets_smaller)
    then show ?thesis
      using assms \<open>q \<in> I\<close> ImmConj unfolding \<O>_def \<O>_conjunct_def by auto
  qed
qed

lemma modal_stability_respecting:
  \<open>stability_respecting (preordered (\<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)))\<close>
  unfolding stability_respecting_def
proof safe
  fix p q
  assume p_stability:
    \<open>preordered (\<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)) p q\<close>
    \<open>stable_state p\<close>
  have \<open>\<not>(\<forall>q'. q \<Zsurj> q'
    \<longrightarrow> \<not> preordered (\<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)) p q' \<or> \<not> stable_state q')\<close>
  proof safe
    assume \<open>\<forall>q'. q \<Zsurj> q'
      \<longrightarrow> \<not> preordered (\<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)) p q' \<or> \<not> stable_state q'\<close>
    hence  \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> stable_state q'
      \<longrightarrow> (\<exists>\<phi> \<in> \<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8). distinguishes \<phi> p q')\<close> by auto
    then obtain \<Phi> where \<Phi>_def:
      \<open>\<forall>q'\<in>(silent_reachable_set {q}). stable_state q'
      \<longrightarrow> distinguishes (\<Phi> q') p q' \<and> \<Phi> q' \<in> \<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)\<close>
      using singleton_iff sreachable_set_is_sreachable by metis
    hence distinctions:
      \<open>\<forall>q'\<in>(silent_reachable_set {q} \<inter> {q'. stable_state q'}). distinguishes (\<Phi> q') p q'\<close>
      \<open>\<forall>q'\<in>(silent_reachable_set {q} \<inter> {q'. stable_state q'}).
        \<Phi> q' \<in> \<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)\<close> by blast+
    from distinction_conjunctification_price[OF this] have
      \<open>\<forall>q'\<in>(silent_reachable_set {q} \<inter> {q'. stable_state q'}).
        conjunctify_distinctions \<Phi> p q' \<in> \<O>_conjunct (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)\<close>
      by fastforce
    hence conj_price: \<open>StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'})
        (conjunctify_distinctions \<Phi> p) \<in> \<O>_inner (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)\<close>
      unfolding \<O>_inner_def \<O>_conjunct_def using SUP_le_iff by fastforce
    from \<Phi>_def have
      \<open>\<forall>q'\<in>(silent_reachable_set {q}). stable_state q'
        \<longrightarrow> hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p q') p q'\<close>
      using singleton_iff distinction_conjunctification by metis
    hence \<open>hml_srbb_inner.distinguishes_from
      (StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'})
        (conjunctify_distinctions \<Phi> p)) p (silent_reachable_set {q})\<close>
      using p_stability(2) by fastforce
    hence
      \<open>distinguishes
        (Internal (StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'})
                (conjunctify_distinctions \<Phi> p))
        )
        p q\<close>
      unfolding silent_reachable_set_def
      using silent_reachable.refl by auto
    moreover have
      \<open>Internal (StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'})
          (conjunctify_distinctions \<Phi> p)) \<in> \<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)\<close>
      using conj_price unfolding \<O>_def \<O>_inner_def by simp
    ultimately show False
      using p_stability(1) preordered_no_distinction by blast
  qed
  thus \<open>\<exists>q'. q \<Zsurj> q' \<and> preordered (\<O> (E e1 e2 e3 \<infinity> e5 \<infinity> e7 e8)) p q' \<and> stable_state q'\<close>
    by blast
qed

end

end
