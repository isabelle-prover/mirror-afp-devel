section \<open>Lemmas about the prover\<close>

theory ProverLemmas imports Prover begin

text \<open>This theory contains a number of lemmas about the prover.
  We will need these when proving soundness and completeness.\<close>

subsection \<open>SeCaV lemmas\<close>
text \<open>We need a few lemmas about the SeCaV system.\<close>

text \<open>Incrementing variable indices does not change the function names in term or a list of terms.\<close>
lemma paramst_liftt [simp]:
  \<open>paramst (liftt t) = paramst t\<close> \<open>paramsts (liftts ts) = paramsts ts\<close>
  by (induct t and ts rule: liftt.induct liftts.induct) auto

text \<open>Subterms do not contain any functions except those in the original term\<close>
lemma paramst_sub_term:
  \<open>paramst (sub_term m s t) \<subseteq> paramst s \<union> paramst t\<close>
  \<open>paramsts (sub_list m s l) \<subseteq> paramst s \<union> paramsts l\<close>
  by (induct t and l rule: sub_term.induct sub_list.induct) auto

text \<open>Substituting a variable for a term does not introduce function names not in that term\<close>
lemma params_sub: \<open>params (sub m t p) \<subseteq> paramst t \<union> params p\<close>
proof (induct p arbitrary: m t)
  case (Pre x1 x2)
  then show ?case
    using paramst_sub_term(2) by simp
qed fastforce+

abbreviation \<open>paramss z \<equiv> \<Union>p \<in> set z. params p\<close>

text \<open>If a function name is fresh, it is not in the list of function names in the sequent\<close>
lemma news_paramss: \<open>news i z \<longleftrightarrow> i \<notin> paramss z\<close>
  by (induct z) auto

text \<open>If a list of terms is a subset of another, the set of function names in it is too\<close>
lemma paramsts_subset: \<open>set A \<subseteq> set B \<Longrightarrow> paramsts A \<subseteq> paramsts B\<close>
  by (induct A) auto

text \<open>Substituting a variable by a term does not change the depth of a formula
  (only the term size changes)\<close>
lemma size_sub [simp]: \<open>size (sub i t p) = size p\<close>
  by (induct p arbitrary: i t) auto

subsection \<open>Fairness\<close>
text \<open>While fairness of the rule stream should be pretty trivial (since we are simply repeating a
  static list of rules forever), the proof is a bit involved.\<close>

text \<open>This function tells us what rule comes next in the stream.\<close>
primrec next_rule :: \<open>rule \<Rightarrow> rule\<close> where
  \<open>next_rule NegNeg = AlphaImp\<close>
| \<open>next_rule AlphaImp = AlphaDis\<close>
| \<open>next_rule AlphaDis = AlphaCon\<close>
| \<open>next_rule AlphaCon = DeltaExi\<close>
| \<open>next_rule DeltaExi = DeltaUni\<close>
| \<open>next_rule DeltaUni = BetaImp\<close>
| \<open>next_rule BetaImp = BetaDis\<close>
| \<open>next_rule BetaDis = BetaCon\<close>
| \<open>next_rule BetaCon = GammaExi\<close>
| \<open>next_rule GammaExi = GammaUni\<close>
| \<open>next_rule GammaUni = NegNeg\<close>

text \<open>This function tells us the index of a rule in the list of rules to repeat.\<close>
primrec rule_index :: \<open>rule \<Rightarrow> nat\<close> where
  \<open>rule_index NegNeg = 0\<close>
| \<open>rule_index AlphaImp = 1\<close>
| \<open>rule_index AlphaDis = 2\<close>
| \<open>rule_index AlphaCon = 3\<close>
| \<open>rule_index DeltaExi = 4\<close>
| \<open>rule_index DeltaUni = 5\<close>
| \<open>rule_index BetaImp = 6\<close>
| \<open>rule_index BetaDis = 7\<close>
| \<open>rule_index BetaCon = 8\<close>
| \<open>rule_index GammaExi = 9\<close>
| \<open>rule_index GammaUni = 10\<close>

text \<open>The list of rules does not have any duplicates.
  This is important because we can then look up rules by their index.\<close>
lemma distinct_rulesList: \<open>distinct rulesList\<close>
  unfolding rulesList_def by simp

text \<open>If you cycle a list, it repeats every \<open>length\<close> elements.\<close>
lemma cycle_nth: \<open>xs \<noteq> [] \<Longrightarrow> cycle xs !! n = xs ! (n mod length xs)\<close>
  by (metis cycle.sel(1) hd_rotate_conv_nth rotate_conv_mod sdrop_cycle sdrop_simps(1))

text \<open>The rule index function can actually be used to look up rules in the list.\<close>
lemma nth_rule_index: \<open>rulesList ! (rule_index r) = r\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma rule_index_bnd: \<open>rule_index r < length rulesList\<close>
  unfolding rulesList_def by (cases r) simp_all

lemma unique_rule_index:
  assumes \<open>n < length rulesList\<close> \<open>rulesList ! n = r\<close>
  shows \<open>n = rule_index r\<close>
  using assms nth_rule_index distinct_rulesList rule_index_bnd nth_eq_iff_index_eq by metis

text \<open>The rule indices repeat in the stream each cycle.\<close>
lemma rule_index_mod:
  assumes \<open>rules !! n = r\<close>
  shows \<open>n mod length rulesList = rule_index r\<close>
proof -
  have *: \<open>rulesList ! (n mod length rulesList) = r\<close>
    using assms cycle_nth unfolding rules_def rulesList_def by (metis list.distinct(1))
  then show ?thesis
    using distinct_rulesList * unique_rule_index
    by (cases r) (metis length_greater_0_conv list.discI rulesList_def
        unique_euclidean_semiring_numeral_class.pos_mod_bound)+
qed

text \<open>We need some lemmas about the modulo function to show that the rules repeat at the right rate.\<close>
lemma mod_hit:
  fixes k :: nat
  assumes \<open>0 < k\<close>
  shows \<open>\<forall>i < k. \<exists>n > m. n mod k = i\<close>
proof safe
  fix i
  let ?n = \<open>(1 + m) * k + i\<close>
  assume \<open>i < k\<close>
  then have \<open>?n mod k = i\<close>
    by (metis mod_less mod_mult_self3)
  moreover have \<open>?n > m\<close>
    using assms
    by (metis One_nat_def Suc_eq_plus1_left Suc_leI add.commute add_lessD1 less_add_one
        mult.right_neutral nat_mult_less_cancel1 order_le_less trans_less_add1 zero_less_one)
  ultimately show \<open>\<exists>n > m. n mod k = i\<close>
    by fast
qed

lemma mod_suff:
  assumes \<open>\<forall>(n :: nat) > m. P (n mod k)\<close> \<open>0 < k\<close>
  shows \<open>\<forall>i < k. P i\<close>
  using assms mod_hit by blast

text \<open>It is always possible to find an index after some point that results in any given rule.\<close>
lemma rules_repeat: \<open>\<exists>n > m. rules !! n = r\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<exists>n > m. rules !! n = r)\<close>
  then have \<open>\<not> (\<exists>n > m. n mod length rulesList = rule_index r)\<close>
    using rule_index_mod nth_rule_index by metis
  then have \<open>\<forall>n > m. n mod length rulesList \<noteq> rule_index r\<close>
    by blast
  moreover have \<open>length rulesList > 0\<close>
    unfolding rulesList_def by simp
  ultimately have \<open>\<forall>k < length rulesList. k \<noteq> rule_index r\<close>
    using mod_suff[where P=\<open>\<lambda>a. a \<noteq> rule_index r\<close>] by blast
  then show False
    using rule_index_bnd by blast
qed

text \<open>It is possible to find such an index no matter where in the stream we start.\<close>
lemma rules_repeat_sdrop: \<open>\<exists>n. (sdrop k rules) !! n = r\<close>
  using rules_repeat by (metis less_imp_add_positive sdrop_snth)

text \<open>Using the lemma above, we prove that the stream of rules is fair by coinduction.\<close>
lemma fair_rules: \<open>fair rules\<close>
proof -
  { fix r assume \<open>r \<in> R\<close>
    then obtain m where r: \<open>r = rules !! m\<close> unfolding sset_range by blast
    { fix n :: nat and rs let ?rules = \<open>\<lambda>n. sdrop n rules\<close>
      assume \<open>n > 0\<close>
      then have \<open>alw (ev (holds ((=) r))) (rs @- ?rules n)\<close>
      proof (coinduction arbitrary: n rs)
        case alw
        show ?case
        proof (rule exI[of _ \<open>rs @- ?rules n\<close>], safe)
          show \<open>\<exists>n' rs'. stl (rs @- ?rules n) = rs' @- ?rules n' \<and> n' > 0\<close>
          proof (cases rs)
            case Nil then show ?thesis unfolding alw
              by (metis sdrop_simps(2) shift.simps(1) zero_less_Suc)
          qed (auto simp: alw intro: exI[of _ n])
        next
          have \<open>ev (holds ((=) r)) (sdrop n rules)\<close>
            unfolding ev_holds_sset using rules_repeat_sdrop by (metis snth_sset)
          then show \<open>ev (holds ((=) r)) (rs @- sdrop n rules)\<close>
            unfolding ev_holds_sset by simp
        qed
      qed
    }
  }
  then show \<open>fair rules\<close> unfolding fair_def
    by (metis (full_types) alw_iff_sdrop ev_holds_sset neq0_conv order_refl sdrop.simps(1)
        stake_sdrop)
qed

subsection \<open>Substitution\<close>
text \<open>We need some lemmas about substitution of variables for terms for the Delta and Gamma rules.\<close>

text \<open>If a term is a subterm of another, so are all of its subterms.\<close>
lemma subtermTm_le: \<open>t \<in> set (subtermTm s) \<Longrightarrow> set (subtermTm t) \<subseteq> set (subtermTm s)\<close>
  by (induct s) auto

text \<open>Trying to substitute a variable that is not in the term does nothing (contrapositively).\<close>
lemma sub_term_const_transfer:
  \<open>sub_term m (Fun a []) t \<noteq> sub_term m s t \<Longrightarrow>
    Fun a [] \<in> set (subtermTm (sub_term m (Fun a []) t))\<close>
  \<open>sub_list m (Fun a []) ts \<noteq> sub_list m s ts \<Longrightarrow>
    Fun a [] \<in> (\<Union>t \<in> set (sub_list m (Fun a []) ts). set (subtermTm t))\<close>
proof (induct t and ts rule: sub_term.induct sub_list.induct)
  case (Var x)
  then show ?case
    by (metis list.set_intros(1) sub_term.simps(1) subtermTm.simps(1))
qed auto

text \<open>If substituting different terms makes a difference, then the substitution has an effect.\<close>
lemma sub_const_transfer:
  assumes \<open>sub m (Fun a []) p \<noteq> sub m t p\<close>
  shows \<open>Fun a [] \<in> set (subtermFm (sub m (Fun a []) p))\<close>
  using assms
proof (induct p arbitrary: m t)
  case (Pre i l)
  then show ?case
    using sub_term_const_transfer(2) by simp
qed auto

text \<open>If the list of subterms is empty for all formulas in a sequent, constant 0 is used instead.\<close>
lemma set_subterms:
  fixes z
  defines \<open>ts \<equiv> \<Union>p \<in> set z. set (subtermFm p)\<close>
  shows \<open>set (subterms z) = (if ts = {} then {Fun 0 []} else ts)\<close>
proof -
  have *: \<open>set (remdups (concat (map subtermFm z))) = (\<Union>p \<in> set z. set (subtermFm p))\<close>
    by (induct z) auto
  then show ?thesis
  proof (cases \<open>ts = {}\<close>)
    case True
    then show ?thesis
      unfolding subterms_def ts_def using *
      by (metis list.simps(15) list.simps(4) set_empty)
  next
    case False
    then show ?thesis
      unfolding subterms_def ts_def using *
      by (metis empty_set list.exhaust list.simps(5))
  qed
qed

text \<open>The parameters and the subterm functions respect each other.\<close>
lemma paramst_subtermTm:
  \<open>\<forall>i \<in> paramst t. \<exists>l. Fun i l \<in> set (subtermTm t)\<close>
  \<open>\<forall>i \<in> paramsts ts. \<exists>l. Fun i l \<in> (\<Union>t \<in> set ts. set (subtermTm t))\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) fastforce+

lemma params_subtermFm: \<open>\<forall>i \<in> params p. \<exists>l. Fun i l \<in> set (subtermFm p)\<close>
proof (induct p)
  case (Pre x1 x2)
  then show ?case
    using paramst_subtermTm by simp
qed auto

lemma subtermFm_subset_params: \<open>set (subtermFm p) \<subseteq> set A \<Longrightarrow> params p \<subseteq> paramsts A\<close>
  using params_subtermFm by force

subsection \<open>Custom cases\<close>
text \<open>Some proofs are more efficient with some custom case lemmas.\<close>

lemma Neg_exhaust
  [case_names Pre Imp Dis Con Exi Uni NegPre NegImp NegDis NegCon NegExi NegUni NegNeg]:
  assumes
    \<open>\<And>i ts. x = Pre i ts \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Imp p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Dis p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Con p q \<Longrightarrow> P\<close>
    \<open>\<And>p. x = Exi p \<Longrightarrow> P\<close>
    \<open>\<And>p. x = Uni p \<Longrightarrow> P\<close>
    \<open>\<And>i ts. x = Neg (Pre i ts) \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Neg (Imp p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Neg (Dis p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. x = Neg (Con p q) \<Longrightarrow> P\<close>
    \<open>\<And>p. x = Neg (Exi p) \<Longrightarrow> P\<close>
    \<open>\<And>p. x = Neg (Uni p) \<Longrightarrow> P\<close>
    \<open>\<And>p. x = Neg (Neg p) \<Longrightarrow> P\<close>
  shows P
  using assms
proof (induct x)
  case (Neg p)
  then show ?case
    by (cases p) simp_all
qed simp_all

lemma parts_exhaust
  [case_names AlphaDis AlphaImp AlphaCon BetaDis BetaImp BetaCon
    DeltaUni DeltaExi NegNeg GammaExi GammaUni Other]:
  assumes
    \<open>\<And>p q. r = AlphaDis \<Longrightarrow> x = Dis p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = AlphaImp \<Longrightarrow> x = Imp p q \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = AlphaCon \<Longrightarrow> x = Neg (Con p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaDis \<Longrightarrow> x = Neg (Dis p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaImp \<Longrightarrow> x = Neg (Imp p q) \<Longrightarrow> P\<close>
    \<open>\<And>p q. r = BetaCon \<Longrightarrow> x = Con p q \<Longrightarrow> P\<close>
    \<open>\<And>p. r = DeltaUni \<Longrightarrow> x = Uni p \<Longrightarrow> P\<close>
    \<open>\<And>p. r = DeltaExi \<Longrightarrow> x = Neg (Exi p) \<Longrightarrow> P\<close>
    \<open>\<And>p. r = NegNeg \<Longrightarrow> x = Neg (Neg p) \<Longrightarrow> P\<close>
    \<open>\<And>p. r = GammaExi \<Longrightarrow> x = Exi p \<Longrightarrow> P\<close>
    \<open>\<And>p. r = GammaUni \<Longrightarrow> x = Neg (Uni p) \<Longrightarrow> P\<close>
    \<open>\<forall>A. parts A r x = [[x]] \<Longrightarrow> P\<close>
  shows P
  using assms
proof (cases r)
  case BetaCon
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (Con p q)
    then show ?thesis
      using BetaCon assms by blast
  qed (simp_all add: parts_def)
next
  case BetaImp
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (NegImp p q)
    then show ?thesis
      using BetaImp assms by blast
  qed (simp_all add: parts_def)
next
  case DeltaUni
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (Uni p)
    then show ?thesis
      using DeltaUni assms by fast
  qed (simp_all add: parts_def)
next
  case DeltaExi
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (NegExi p)
    then show ?thesis
      using DeltaExi assms by fast
  qed (simp_all add: parts_def)
next
  case n: NegNeg
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (NegNeg p)
    then show ?thesis
      using n assms by fast
  qed (simp_all add: parts_def)
next
  case GammaExi
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (Exi p)
    then show ?thesis
      using GammaExi assms by fast
  qed (simp_all add: parts_def)
next
  case GammaUni
  then show ?thesis
    using assms
  proof (cases x rule: Neg_exhaust)
    case (NegUni p)
    then show ?thesis
      using GammaUni assms by fast
  qed (simp_all add: parts_def)
qed (cases x rule: Neg_exhaust, simp_all add: parts_def)+

subsection \<open>Unaffected formulas\<close>
text \<open>We need some lemmas to show that formulas to which rules do not apply are not lost.\<close>

text \<open>This function returns True if the rule applies to the formula, and False otherwise.\<close>
definition affects :: \<open>rule \<Rightarrow> fm \<Rightarrow> bool\<close> where
  \<open>affects r p \<equiv> case (r, p) of
    (AlphaDis, Dis _ _) \<Rightarrow> True
  | (AlphaImp, Imp _ _) \<Rightarrow> True
  | (AlphaCon, Neg (Con _ _)) \<Rightarrow> True
  | (BetaCon, Con _ _) \<Rightarrow> True
  | (BetaImp, Neg (Imp _ _)) \<Rightarrow> True
  | (BetaDis, Neg (Dis _ _)) \<Rightarrow> True
  | (DeltaUni, Uni _) \<Rightarrow> True
  | (DeltaExi, Neg (Exi _)) \<Rightarrow> True
  | (NegNeg, Neg (Neg _)) \<Rightarrow> True
  | (GammaExi, Exi _) \<Rightarrow> False
  | (GammaUni, Neg (Uni _)) \<Rightarrow> False
  | (_,  _) \<Rightarrow> False\<close>

text \<open>If a rule does not affect a formula, that formula will be in the sequent obtained after
  applying the rule.\<close>
lemma parts_preserves_unaffected:
  assumes \<open>\<not> affects r p\<close> \<open>z' \<in> set (parts A r p)\<close>
  shows \<open>p \<in> set z'\<close>
  using assms unfolding affects_def
  by (cases r p rule: parts_exhaust) (simp_all add: parts_def)

text \<open>The \<open>list_prod\<close> function computes the Cartesian product.\<close>
lemma list_prod_is_cartesian:
  \<open>set (list_prod hs ts) = {h @ t |h t. h \<in> set hs \<and> t \<in> set ts}\<close>
  by (induct ts) auto

text \<open>The \<open>children\<close> function produces the Cartesian product of the branches from the first formula
and the branches from the rest of the sequent.\<close>
lemma set_children_Cons:
  \<open>set (children A r (p # z)) =
    {hs @ ts |hs ts. hs \<in> set (parts A r p) \<and>
      ts \<in> set (children (remdups (A @ subtermFms (concat (parts A r p)))) r z)}\<close>
  using list_prod_is_cartesian by (metis children.simps(2))

text \<open>The \<open>children\<close> function does not change unaffected formulas.\<close>
lemma children_preserves_unaffected:
  assumes \<open>p \<in> set z\<close> \<open>\<not> affects r p\<close> \<open>z' \<in> set (children A r z)\<close>
  shows \<open>p \<in> set z'\<close>
  using assms parts_preserves_unaffected set_children_Cons
  by (induct z arbitrary: A z') auto

text \<open>The \<open>effect\<close> function does not change unaffected formulas.\<close>
lemma effect_preserves_unaffected:
  assumes \<open>p \<in> set z\<close> and \<open>\<not> affects r p\<close> and \<open>(B, z') |\<in>| effect r (A, z)\<close>
  shows \<open>p \<in> set z'\<close>
  using assms children_preserves_unaffected
  unfolding effect_def
  by (smt (verit, best) Pair_inject femptyE fimageE fset_of_list_elem old.prod.case)

subsection \<open>Affected formulas\<close>
text \<open>We need some lemmas to show that formulas to which rules do apply are decomposed into their
  constituent parts correctly.\<close>

text \<open>If a formula occurs in a sequent on a child branch generated by \<open>children\<close>, it was part of
  the current sequent.\<close>
lemma parts_in_children:
  assumes \<open>p \<in> set z\<close> \<open>z' \<in> set (children A r z)\<close>
  shows \<open>\<exists>B xs. set A \<subseteq> set B \<and> xs \<in> set (parts B r p) \<and> set xs \<subseteq> set z'\<close>
  using assms
proof (induct z arbitrary: A z')
  case (Cons a _)
  then show ?case
  proof (cases \<open>a = p\<close>)
    case True
    then show ?thesis
      using Cons(3) set_children_Cons by fastforce
  next
    case False
    then show ?thesis
      using Cons set_children_Cons
      by (smt (verit, del_insts) le_sup_iff mem_Collect_eq set_ConsD set_append set_remdups subset_trans sup_ge2)
  qed
qed simp

text \<open>If \<open>effect\<close> contains something, then the input sequent is not an axiom.\<close>
lemma ne_effect_not_branchDone: \<open>(B, z') |\<in>| effect r (A, z) \<Longrightarrow> \<not> branchDone z\<close>
  by (cases \<open>branchDone z\<close>) simp_all

text \<open>The \<open>effect\<close> function decomposes formulas in the sequent using the \<open>parts\<close> function.
  (Unless the sequent is an axiom, in which case no child branches are generated.)\<close>
lemma parts_in_effect:
  assumes \<open>p \<in> set z\<close> and \<open>(B, z') |\<in>| effect r (A, z)\<close>
  shows \<open>\<exists>C xs. set A \<subseteq> set C \<and> xs \<in> set (parts C r p) \<and> set xs \<subseteq> set z'\<close>
  using assms parts_in_children ne_effect_not_branchDone
  by (smt (verit, ccfv_threshold) Pair_inject effect.simps fimageE fset_of_list_elem le_sup_iff
      set_append set_remdups)

text \<open>Specifically, this applied to the double negation elimination rule and the GammaUni rule.\<close>
corollary \<open>Neg (Neg p) \<in> set z \<Longrightarrow> (B, z') |\<in>| effect NegNeg (A, z) \<Longrightarrow> p \<in> set z'\<close>
  using parts_in_effect unfolding parts_def by fastforce

corollary \<open>Neg (Uni p) \<in> set z \<Longrightarrow> (B, z') |\<in>| effect GammaUni (A, z) \<Longrightarrow>
    set (map (\<lambda>t. Neg (sub 0 t p)) A) \<subseteq> set z'\<close>
  using parts_in_effect unfolding parts_def by fastforce

text \<open>If the sequent is not an axiom, and the rule and sequent match, all of the child branches
  generated by \<open>children\<close> will be included in the proof tree.\<close>
lemma eff_children:
  assumes \<open>\<not> branchDone z\<close> \<open>eff r (A, z) ss\<close>
  shows \<open>\<forall>z' \<in> set (children (remdups (A @ subtermFms z)) r z). \<exists>B. (B, z') |\<in>| ss\<close>
  using assms unfolding eff_def using fset_of_list_elem by fastforce

subsection \<open>Generating new function names\<close>
text \<open>We need to show that the \<open>generateNew\<close> function actually generates new function names.
  This requires a few lemmas about the interplay between \<open>max\<close> and \<open>foldr\<close>.\<close>

lemma foldr_max:
  fixes xs :: \<open>nat list\<close>
  shows \<open>foldr max xs 0 = (if xs = [] then 0 else Max (set xs))\<close>
  by (induct xs) simp_all

lemma Suc_max_new:
  fixes xs :: \<open>nat list\<close>
  shows \<open>Suc (foldr max xs 0) \<notin> set xs\<close>
proof (cases xs)
  case (Cons x xs)
  then have \<open>foldr max (x # xs) 0 = Max (set (x # xs))\<close>
    using foldr_max by simp
  then show ?thesis
    using Cons by (metis List.finite_set Max.insert add_0 empty_iff list.set(2) max_0_1(2)
        n_not_Suc_n nat_add_max_left plus_1_eq_Suc remdups.simps(2) set_remdups)
qed simp

lemma listFunTm_paramst: \<open>set (listFunTm t) = paramst t\<close> \<open>set (listFunTms ts) = paramsts ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

subsection \<open>Finding axioms\<close>

text \<open>The \<open>branchDone\<close> function correctly determines whether a sequent is an axiom.\<close>
lemma branchDone_contradiction: \<open>branchDone z \<longleftrightarrow> (\<exists>p. p \<in> set z \<and> Neg p \<in> set z)\<close>
  by (induct z rule: branchDone.induct) auto

subsection \<open>Subterms\<close>
text \<open>We need a few lemmas about the behaviour of our subterm functions.\<close>

text \<open>Any term is a subterm of itself.\<close>
lemma subtermTm_refl [simp]: \<open>t \<in> set (subtermTm t)\<close>
  by (induct t) simp_all

text \<open>The arguments of a predicate are subterms of it.\<close>
lemma subterm_Pre_refl: \<open>set ts \<subseteq> set (subtermFm (Pre n ts))\<close>
  by (induct ts) auto

text \<open>The arguments of function are subterms of it.\<close>
lemma subterm_Fun_refl: \<open>set ts \<subseteq> set (subtermTm (Fun n ts))\<close>
  by (induct ts) auto

text \<open>This function computes the predicates in a formula.
  We will use this function to help prove the final lemma in this section.\<close>
primrec preds :: \<open>fm \<Rightarrow> fm set\<close> where
  \<open>preds (Pre n ts) = {Pre n ts}\<close>
| \<open>preds (Imp p q) = preds p \<union> preds q\<close>
| \<open>preds (Dis p q) = preds p \<union> preds q\<close>
| \<open>preds (Con p q) = preds p \<union> preds q\<close>
| \<open>preds (Exi p) = preds p\<close>
| \<open>preds (Uni p) = preds p\<close>
| \<open>preds (Neg p) = preds p\<close>

text \<open>If a term is a subterm of a formula, it is a subterm of some predicate in the formula.\<close>
lemma subtermFm_preds: \<open>t \<in> set (subtermFm p) \<longleftrightarrow> (\<exists>pre \<in> preds p. t \<in> set (subtermFm pre))\<close>
  by (induct p) auto

lemma preds_shape: \<open>pre \<in> preds p \<Longrightarrow> \<exists>n ts. pre = Pre n ts\<close>
  by (induct p) auto

text \<open>If a function is a subterm of a formula, so are the arguments of that function.\<close>
lemma fun_arguments_subterm:
  assumes \<open>Fun n ts \<in> set (subtermFm p)\<close>
  shows \<open>set ts \<subseteq> set (subtermFm p)\<close>
proof -
  obtain pre where pre: \<open>pre \<in> preds p\<close> \<open>Fun n ts \<in> set (subtermFm pre)\<close>
    using assms subtermFm_preds by blast
  then obtain n' ts' where \<open>pre = Pre n' ts'\<close>
    using preds_shape by blast
  then have \<open>set ts \<subseteq> set (subtermFm pre)\<close>
    using subtermTm_le pre by force
  then have \<open>set ts \<subseteq> set (subtermFm p)\<close>
    using pre subtermFm_preds by blast
  then show ?thesis
    by blast
qed

end
