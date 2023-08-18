(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>A Concrete Unification Algorithm\<close>

theory Unification
  imports
    Abstract_Unification
    Option_Monad
    Renaming2
begin

definition
  "decompose s t =
    (case (s, t) of
      (Fun f ss, Fun g ts) \<Rightarrow> if f = g then zip_option ss ts else None
    | _ \<Rightarrow> None)"

lemma decompose_same_Fun[simp]: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "decompose (Fun f ss) (Fun f ss) = Some (zip ss ss)"
  by (simp add: decompose_def)

lemma decompose_Some [dest]:
  "decompose (Fun f ss) (Fun g ts) = Some E \<Longrightarrow>
    f = g \<and> length ss = length ts \<and> E = zip ss ts"
  by (cases "f = g") (auto simp: decompose_def)

lemma decompose_None [dest]:
  "decompose (Fun f ss) (Fun g ts) = None \<Longrightarrow> f \<noteq> g \<or> length ss \<noteq> length ts"
  by (cases "f = g") (auto simp: decompose_def)

text \<open>Applying a substitution to a list of equations.\<close>
definition
  subst_list :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation list \<Rightarrow> ('f, 'v) equation list"
  where
    "subst_list \<sigma> ys = map (\<lambda>p. (fst p \<cdot> \<sigma>, snd p \<cdot> \<sigma>)) ys"

lemma mset_subst_list [simp]:
  "mset (subst_list (subst x t) ys) = subst_mset (subst x t) (mset ys)"
  by (auto simp: subst_mset_def subst_list_def)

lemma subst_list_append:
  "subst_list \<sigma> (xs @ ys) = subst_list \<sigma> xs @ subst_list \<sigma> ys"
by (auto simp: subst_list_def)

function (sequential)
  unify ::
    "('f, 'v) equation list \<Rightarrow> ('v \<times> ('f, 'v) term) list \<Rightarrow> ('v \<times> ('f, 'v) term) list option"
where
  "unify [] bs = Some bs"
| "unify ((Fun f ss, Fun g ts) # E) bs =
    (case decompose (Fun f ss) (Fun g ts) of
      None \<Rightarrow> None
    | Some us \<Rightarrow> unify (us @ E) bs)"
| "unify ((Var x, t) # E) bs =
    (if t = Var x then unify E bs
    else if x \<in> vars_term t then None
    else unify (subst_list (subst x t) E) ((x, t) # bs))"
| "unify ((t, Var x) # E) bs =
    (if x \<in> vars_term t then None
    else unify (subst_list (subst x t) E) ((x, t) # bs))"
  by pat_completeness auto
termination
  by (standard, rule wf_inv_image [of "unif\<inverse>" "mset \<circ> fst", OF wf_converse_unif])
     (force intro: UNIF1.intros simp: unif_def union_commute)+

lemma unify_append_prefix_same: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "(\<forall>e \<in> set es1. fst e = snd e) \<Longrightarrow> unify (es1 @ es2) bs = unify es2 bs"
proof (induction "es1 @ es2" bs arbitrary: es1 es2 bs rule: unify.induct)
  case (1 bs)
  thus ?case by simp
next
  case (2 f ss g ts E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun f ss, Fun g ts)" and E_def: "E = es1' @ es2"
      using "2" by simp_all
    hence "f = g" and "ss = ts"
      using "2.prems" local.Cons by auto
    hence "unify (es1 @ es2) bs = unify ((zip ts ts @ es1') @ es2) bs"
      by (simp add: Cons e_def)
    also have "\<dots> = unify es2 bs"
    proof (rule "2.hyps"(1))
      show "decompose (Fun f ss) (Fun g ts) = Some (zip ts ts)"
        by (simp add: \<open>f = g\<close> \<open>ss = ts\<close>)
    next
      show "zip ts ts @ E = (zip ts ts @ es1') @ es2"
        by (simp add: E_def)
    next
      show "\<forall>e\<in>set (zip ts ts @ es1'). fst e = snd e"
        using "2.prems" by (auto simp: Cons zip_same)
    qed
    finally show ?thesis .
  qed
next
  case (3 x t E bs)
  show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Var x, t)" and E_def: "E = es1' @ es2"
      using 3 by simp_all
    show ?thesis
    proof (cases "t = Var x")
      case True
      show ?thesis
        using 3(1)[OF True E_def]
        using "3.hyps"(3) "3.prems" local.Cons by fastforce
    next
      case False
      thus ?thesis
        using "3.prems" e_def local.Cons by force
    qed
  qed
next
  case (4 v va x E bs)
  then show ?case
  proof (cases es1)
    case Nil
    thus ?thesis by simp
  next
    case (Cons e es1')
    hence e_def: "e = (Fun v va, Var x)" and E_def: "E = es1' @ es2"
      using 4 by simp_all
    thus ?thesis
      using "4.prems" local.Cons by fastforce
  qed
qed

corollary unify_Cons_same: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "fst e = snd e \<Longrightarrow> unify (e # es) bs = unify es bs"
  by (rule unify_append_prefix_same[of "[_]", simplified])

corollary unify_same: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "(\<forall>e \<in> set es. fst e = snd e) \<Longrightarrow> unify es bs = Some bs"
  by (rule unify_append_prefix_same[of _ "[]", simplified])

definition subst_of :: "('v \<times> ('f, 'v) term) list \<Rightarrow> ('f, 'v) subst"
  where
    "subst_of ss = List.foldr (\<lambda>(x, t) \<sigma>. \<sigma> \<circ>\<^sub>s subst x t) ss Var"

text \<open>Computing the mgu of two terms.\<close>
definition mgu :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst option" where
  "mgu s t =
    (case unify [(s, t)] [] of
      None \<Rightarrow> None
    | Some res \<Rightarrow> Some (subst_of res))"

lemma subst_of_simps [simp]:
  "subst_of [] = Var"
  "subst_of ((x, Var x) # ss) = subst_of ss"
  "subst_of (b # ss) = subst_of ss \<circ>\<^sub>s subst (fst b) (snd b)"
  by (simp_all add: subst_of_def split: prod.splits)

lemma subst_of_append [simp]:
  "subst_of (ss @ ts) = subst_of ts \<circ>\<^sub>s subst_of ss"
  by (induct ss) (auto simp: ac_simps)

text \<open>The concrete algorithm \<open>unify\<close> can be simulated by the inference
  rules of \<open>UNIF\<close>.\<close>
lemma unify_Some_UNIF:
  assumes "unify E bs = Some cs"
  shows "\<exists>ds ss. cs = ds @ bs \<and> subst_of ds = compose ss \<and> UNIF ss (mset E) {#}"
using assms
proof (induction E bs arbitrary: cs rule: unify.induct)
  case (2 f ss g ts E bs)
  then obtain us where "decompose (Fun f ss) (Fun g ts) = Some us"
    and [simp]: "f = g" "length ss = length ts" "us = zip ss ts"
    and "unify (us @ E) bs = Some cs" by (auto split: option.splits)
  from "2.IH" [OF this(1, 5)] obtain xs ys
    where "cs = xs @ bs"
    and [simp]: "subst_of xs = compose ys"
    and *: "UNIF ys (mset (us @ E)) {#}" by auto
  then have "UNIF (Var # ys) (mset ((Fun f ss, Fun g ts) # E)) {#}"
    by (force intro: UNIF1.decomp simp: ac_simps)
  moreover have "cs = xs @ bs" by fact
  moreover have "subst_of xs = compose (Var # ys)" by simp
  ultimately show ?case by blast
next
  case (3 x t E bs)
  show ?case
  proof (cases "t = Var x")
    assume "t = Var x"
    then show ?case
      using 3 by auto (metis UNIF.step compose_simps(2) UNIF1.trivial)
  next
    assume "t \<noteq> Var x"
    with 3 obtain xs ys
      where [simp]: "cs = (ys @ [(x, t)]) @ bs"
      and [simp]: "subst_of ys = compose xs"
      and "x \<notin> vars_term t"
      and "UNIF xs (mset (subst_list (subst x t) E)) {#}"
        by (cases "x \<in> vars_term t") force+
    then have "UNIF (subst x t # xs) (mset ((Var x, t) # E)) {#}"
      by (force intro: UNIF1.Var_left simp: ac_simps)
    moreover have "cs = (ys @ [(x, t)]) @ bs" by simp
    moreover have "subst_of (ys @ [(x, t)]) = compose (subst x t # xs)" by simp
    ultimately show ?case by blast
  qed
next
  case (4 f ss x E bs)
  with 4 obtain xs ys
    where [simp]: "cs = (ys @ [(x, Fun f ss)]) @ bs"
    and [simp]: "subst_of ys = compose xs"
    and "x \<notin> vars_term (Fun f ss)"
    and "UNIF xs (mset (subst_list (subst x (Fun f ss)) E)) {#}"
      by (cases "x \<in> vars_term (Fun f ss)") force+
  then have "UNIF (subst x (Fun f ss) # xs) (mset ((Fun f ss, Var x) # E)) {#}"
    by (force intro: UNIF1.Var_right simp: ac_simps)
  moreover have "cs = (ys @ [(x, Fun f ss)]) @ bs" by simp
  moreover have "subst_of (ys @ [(x, Fun f ss)]) = compose (subst x (Fun f ss) # xs)" by simp
  ultimately show ?case by blast
qed force

lemma unify_sound:
  assumes "unify E [] = Some cs"
  shows "is_imgu (subst_of cs) (set E)"
proof -
  from unify_Some_UNIF [OF assms] obtain ss
    where "subst_of cs = compose ss"
    and "UNIF ss (mset E) {#}" by auto
  with UNIF_empty_imp_is_mgu_compose [OF this(2)]
    and UNIF_idemp [OF this(2)]
    show ?thesis
      by (auto simp add: is_imgu_def is_mgu_def)
         (metis subst_compose_assoc)
qed

lemma mgu_sound:
  assumes "mgu s t = Some \<sigma>"
  shows "is_imgu \<sigma> {(s, t)}"
proof -
  obtain ss where "unify [(s, t)] [] = Some ss"
    and "\<sigma> = subst_of ss"
    using assms by (auto simp: mgu_def split: option.splits)
  then have "is_imgu \<sigma> (set [(s, t)])" by (metis unify_sound)
  then show ?thesis by simp
qed

text \<open>If \<open>unify\<close> gives up, then the given set of equations
  cannot be reduced to the empty set by \<open>UNIF\<close>.\<close>
lemma unify_None:
  assumes "unify E ss = None"
  shows "\<exists>E'. E' \<noteq> {#} \<and> (mset E, E') \<in> unif\<^sup>!"
using assms
proof (induction E ss rule: unify.induct)
  case (1 bs)
  then show ?case by simp
next
  case (2 f ss g ts E bs)
  moreover
  { assume *: "decompose (Fun f ss) (Fun g ts) = None"
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(Fun f ss, Fun g ts)#}"] obtain \<sigma>
        where "(mset E + {#(Fun f ss, Fun g ts)#}, {#(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover have "{#(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>)#} \<in> NF unif"
        using decompose_None [OF *]
        by (auto simp: single_is_union NF_def unif_def elim!: UNIF1.cases)
           (metis length_map)
      ultimately show ?thesis
        by auto (metis normalizability_I add_mset_not_empty)
    next
      case False
      moreover have "\<not> unifiable {(Fun f ss, Fun g ts)}"
        using * by (auto simp: unifiable_def)
      ultimately have "\<not> unifiable (set ((Fun f ss, Fun g ts) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis by (simp add: not_unifiable_imp_not_empty_NF)
    qed }
  moreover
  { fix us
    assume *: "decompose (Fun f ss) (Fun g ts) = Some us"
      and "unify (us @ E) bs = None"
    from "2.IH" [OF this] obtain E'
      where "E' \<noteq> {#}" and "(mset (us @ E), E') \<in> unif\<^sup>!" by blast
    moreover have "(mset ((Fun f ss, Fun g ts) # E), mset (us @ E)) \<in> unif"
    proof -
      have "g = f" and "length ss = length ts" and "us = zip ss ts"
        using * by auto
      then show ?thesis
        by (auto intro: UNIF1.decomp simp: unif_def ac_simps)
    qed
    ultimately have ?case by auto }
  ultimately show ?case by (auto split: option.splits)
next
  case (3 x t E bs)
  { assume [simp]: "t = Var x"
    obtain E' where "E' \<noteq> {#}" and "(mset E, E') \<in> unif\<^sup>!" using 3 by auto
    moreover have "(mset ((Var x, t) # E), mset E) \<in> unif"
      by (auto intro: UNIF1.trivial simp: unif_def)
    ultimately have ?case by auto }
  moreover
  { assume *: "t \<noteq> Var x" "x \<notin> vars_term t"
    then obtain E' where "E' \<noteq> {#}"
      and "(mset (subst_list (subst x t) E), E') \<in> unif\<^sup>!" using 3 by auto
    moreover have "(mset ((Var x, t) # E), mset (subst_list (subst x t) E)) \<in> unif"
      using * by (auto intro: UNIF1.Var_left simp: unif_def)
    ultimately have ?case by auto }
  moreover
  { assume *: "t \<noteq> Var x" "x \<in> vars_term t"
    then have "x \<in> vars_term t" "is_Fun t" by auto
    then have "\<not> unifiable {(Var x, t)}" by (rule in_vars_is_Fun_not_unifiable)
    then have **: "\<not> unifiable {(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)}" for \<sigma> :: "('b, 'a) subst"
      using subst_set_reflects_unifiable [of \<sigma> "{(Var x, t)}"] by (auto simp: subst_set_def)
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(Var x, t)#}"] obtain \<sigma>
        where "(mset E + {#(Var x, t)#}, {#(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover obtain E' where "E' \<noteq> {#}"
        and "({#(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)#}, E') \<in> unif\<^sup>!"
        using not_unifiable_imp_not_empty_NF and **
          by (metis set_mset_single)
      ultimately show ?thesis by auto
    next
      case False
      moreover have "\<not> unifiable {(Var x, t)}"
        using * by (force simp: unifiable_def)
      ultimately have "\<not> unifiable (set ((Var x, t) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis
        by (simp add: not_unifiable_imp_not_empty_NF)
    qed }
  ultimately show ?case by blast
next
  case (4 f ss x E bs)
  define t where "t = Fun f ss"
  { assume *: "x \<notin> vars_term t"
    then obtain E' where "E' \<noteq> {#}"
      and "(mset (subst_list (subst x t) E), E') \<in> unif\<^sup>!" using 4 by (auto simp: t_def)
    moreover have "(mset ((t, Var x) # E), mset (subst_list (subst x t) E)) \<in> unif"
      using * by (auto intro: UNIF1.Var_right simp: unif_def)
    ultimately have ?case by (auto simp: t_def) }
  moreover
  { assume "x \<in> vars_term t"
    then have *: "x \<in> vars_term t" "t \<noteq> Var x" by (auto simp: t_def)
    then have "x \<in> vars_term t" "is_Fun t" by auto
    then have "\<not> unifiable {(Var x, t)}" by (rule in_vars_is_Fun_not_unifiable)
    then have **: "\<not> unifiable {(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)}" for \<sigma> :: "('b, 'a) subst"
      using subst_set_reflects_unifiable [of \<sigma> "{(Var x, t)}"] by (auto simp: subst_set_def)
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(t, Var x)#}"] obtain \<sigma>
        where "(mset E + {#(t, Var x)#}, {#(t \<cdot> \<sigma>, Var x \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover obtain E' where "E' \<noteq> {#}"
        and "({#(t \<cdot> \<sigma>, Var x \<cdot> \<sigma>)#}, E') \<in> unif\<^sup>!"
        using not_unifiable_imp_not_empty_NF and **
          by (metis unifiable_insert_swap set_mset_single)
      ultimately show ?thesis by (auto simp: t_def)
    next
      case False
      moreover have "\<not> unifiable {(t, Var x)}"
        using * by (simp add: unifiable_def)
      ultimately have "\<not> unifiable (set ((t, Var x) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis by (simp add: not_unifiable_imp_not_empty_NF t_def)
    qed }
  ultimately show ?case by blast
qed

lemma unify_complete:
  assumes "unify E bs = None"
  shows "unifiers (set E) = {}"
proof -
  from unify_None [OF assms] obtain E'
    where "E' \<noteq> {#}" and "(mset E, E') \<in> unif\<^sup>!" by blast
  then have "\<not> unifiable (set E)"
    using irreducible_reachable_imp_not_unifiable by force
  then show ?thesis
    by (auto simp: unifiable_def)
qed

corollary ex_unify_if_unifiers_not_empty: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "unifiers es \<noteq> {} \<Longrightarrow> set xs = es \<Longrightarrow> \<exists>ys. unify xs [] = Some ys"
  using unify_complete by auto

lemma mgu_complete:
  "mgu s t = None \<Longrightarrow> unifiers {(s, t)} = {}"
proof -
  assume "mgu s t = None"
  then have "unify [(s, t)] [] = None" by (cases "unify [(s, t)] []", auto simp: mgu_def)
  then have "unifiers (set [(s, t)]) = {}" by (rule unify_complete)
  then show ?thesis by simp
qed

corollary ex_mgu_if_unifiers_not_empty: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "unifiers {(t,u)} \<noteq> {} \<Longrightarrow> \<exists>\<mu>. mgu t u = Some \<mu>"
  using mgu_complete by auto

corollary ex_mgu_if_subst_apply_term_eq_subst_apply_term: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes t u :: "('f, 'v) Term.term" and \<sigma> :: "('f, 'v) subst"
  assumes t_eq_u: "t \<cdot> \<sigma> = u \<cdot> \<sigma>"
  shows "\<exists>\<mu> :: ('f, 'v) subst. Unification.mgu t u = Some \<mu>"
proof -
  from t_eq_u have "unifiers {(t, u)} \<noteq> {}"
    unfolding unifiers_def by auto
  thus ?thesis
    by (rule ex_mgu_if_unifiers_not_empty)
qed

lemma finite_subst_domain_subst_of:
  "finite (subst_domain (subst_of xs))"
proof (induct xs)
  case (Cons x xs)
  moreover have "finite (subst_domain (subst (fst x) (snd x)))" by (metis finite_subst_domain_subst)
  ultimately show ?case
    using subst_domain_compose [of "subst_of xs" "subst (fst x) (snd x)"]
    by (simp del: subst_subst_domain) (metis finite_subset infinite_Un)
qed simp

lemma unify_subst_domain: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes unif: "unify E [] = Some xs"
  shows "subst_domain (subst_of xs) \<subseteq> (\<Union>e \<in> set E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_subst_domain_subset
    by (metis (mono_tags, lifting) multiset.set_map set_mset_mset vars_mset_def)
qed

lemma mgu_subst_domain:
  assumes "mgu s t = Some \<sigma>"
  shows "subst_domain \<sigma> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where "unify [(s, t)] [] = Some xs" and "\<sigma> = subst_of xs"
    using assms by (simp add: mgu_def split: option.splits)
  thus ?thesis
    using unify_subst_domain by fastforce
qed

lemma mgu_finite_subst_domain:
  "mgu s t = Some \<sigma> \<Longrightarrow> finite (subst_domain \<sigma>)"
  by (drule mgu_subst_domain) (simp add: finite_subset)

lemma unify_range_vars: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes unif: "unify E [] = Some xs"
  shows "range_vars (subst_of xs) \<subseteq> (\<Union>e \<in> set E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_range_vars_subset
    by (metis (mono_tags, lifting) multiset.set_map set_mset_mset vars_mset_def)
qed

lemma mgu_range_vars: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "mgu s t = Some \<mu>"
  shows "range_vars \<mu> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where "unify [(s, t)] [] = Some xs" and "\<mu> = subst_of xs"
    using assms by (simp add: mgu_def split: option.splits)
  thus ?thesis
    using unify_range_vars by fastforce
qed

lemma unify_subst_domain_range_vars_disjoint: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes unif: "unify E [] = Some xs"
  shows "subst_domain (subst_of xs) \<inter> range_vars (subst_of xs) = {}"
proof -
  from unify_Some_UNIF[OF unif] obtain xs' where
    "subst_of xs = compose xs'" and "UNIF xs' (mset E) {#}"
    by auto
  thus ?thesis
    using UNIF_subst_domain_range_vars_Int by metis
qed

lemma mgu_subst_domain_range_vars_disjoint: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes "mgu s t = Some \<mu>"
  shows "subst_domain \<mu> \<inter> range_vars \<mu> = {}"
proof -
  obtain xs where "unify [(s, t)] [] = Some xs" and "\<mu> = subst_of xs"
    using assms by (simp add: mgu_def split: option.splits)
  thus ?thesis
    using unify_subst_domain_range_vars_disjoint by metis
qed

corollary subst_apply_term_eq_subst_apply_term_if_mgu: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes mgu_t_u: "mgu t u = Some \<mu>"
  shows "t \<cdot> \<mu> = u \<cdot> \<mu>"
  using mgu_sound[OF mgu_t_u]
  by (simp add: is_imgu_def unifiers_def)

lemma mgu_same: "mgu t t = Some Var" \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  by (simp add: mgu_def unify_same)

lemma mgu_is_Var_if_not_in_equations: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and x :: 'v
  assumes
    mgu_\<mu>: "is_mgu \<mu> E" and
    x_not_in: "x \<notin> (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "is_Var (\<mu> x)"
proof -
  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>"
      by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv
      by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>"
      by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<mu> \<circ>\<^sub>s \<gamma> = \<tau>"
    by auto
  with x_not_in have "(\<mu> \<circ>\<^sub>s \<gamma>) x = Var x"
    by (simp add: \<tau>_def)
  thus "is_Var (\<mu> x)"
    by (metis subst_apply_eq_Var subst_compose term.disc(1))
qed

corollary mgu_ball_is_Var: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "is_mgu \<mu> E \<Longrightarrow> \<forall>x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e)). is_Var (\<mu> x)"
  by (rule ballI) (rule mgu_is_Var_if_not_in_equations[folded Compl_iff])

lemma mgu_inj_on: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations"
  assumes mgu_\<mu>: "is_mgu \<mu> E"
  shows "inj_on \<mu> (- (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)))"
proof (rule inj_onI)
  fix x y
  assume
    x_in: "x \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    y_in: "y \<in> - (\<Union>e\<in>E. vars_term (fst e) \<union> vars_term (snd e))" and
    "\<mu> x = \<mu> y"

  from mgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>"
    by (simp_all add: is_mgu_def)

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = (\<lambda>x. if x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)) then \<mu> x else Var x)"

  have \<open>\<tau> \<in> unifiers E\<close>
    unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e assume "e \<in> E"
    with unif_\<mu> have "fst e \<cdot> \<mu> = snd e \<cdot> \<mu>"
      by blast
    moreover from \<open>e \<in> E\<close> have "fst e \<cdot> \<tau> = fst e \<cdot> \<mu>" and "snd e \<cdot> \<tau> = snd e \<cdot> \<mu>"
      unfolding term_subst_eq_conv
      by (auto simp: \<tau>_def)
    ultimately show "fst e \<cdot> \<tau> = snd e \<cdot> \<tau>"
      by simp
  qed
  with minimal_\<mu> obtain \<gamma> where "\<mu> \<circ>\<^sub>s \<gamma> = \<tau>"
    by auto
  hence "(\<mu> \<circ>\<^sub>s \<gamma>) x = Var x" and "(\<mu> \<circ>\<^sub>s \<gamma>) y = Var y"
    using ComplD[OF x_in] ComplD[OF y_in]
    by (simp_all add: \<tau>_def)
  with \<open>\<mu> x = \<mu> y\<close> show "x = y"
    by (simp add: subst_compose_def)
qed

lemma imgu_subst_domain_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and Evars :: "'v set"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  defines "Evars \<equiv> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "subst_domain \<mu> \<subseteq> Evars"
proof (intro Set.subsetI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<mu> \<circ>\<^sub>s \<tau> = \<tau>"
    by (simp_all add: is_imgu_def)

  from fin_E obtain es :: "('f, 'v) equation list" where
    "set es = E"
    using finite_list by auto
  then obtain xs :: "('v \<times> ('f, 'v) Term.term) list" where
    unify_es: "unify es [] = Some xs"
    using unif_\<mu> ex_unify_if_unifiers_not_empty by blast

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = subst_of xs"

  have dom_\<tau>: "subst_domain \<tau> \<subseteq> Evars"
    using unify_subst_domain[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  have range_vars_\<tau>: "range_vars \<tau> \<subseteq> Evars"
    using unify_range_vars[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .

  have "\<tau> \<in> unifiers E"
    using \<open>set es = E\<close> unify_es \<tau>_def is_imgu_def unify_sound by blast
  with minimal_\<mu> have \<mu>_comp_\<tau>: "\<And>x. (\<mu> \<circ>\<^sub>s \<tau>) x = \<tau> x"
    by auto

  fix x :: 'v assume "x \<in> subst_domain \<mu>"
  hence "\<mu> x \<noteq> Var x"
    by (simp add: subst_domain_def)

  show "x \<in> Evars"
  proof (cases "x \<in> subst_domain \<tau>")
    case True
    thus ?thesis
      using dom_\<tau> by auto
  next
    case False
    hence "\<tau> x = Var x"
      by (simp add: subst_domain_def)
    hence "\<mu> x \<cdot> \<tau> = Var x"
      using \<mu>_comp_\<tau>[of x] by (simp add: subst_compose)
    thus ?thesis
    proof (rule subst_apply_eq_Var)
      show "\<And>y. \<mu> x = Var y \<Longrightarrow> \<tau> y = Var x \<Longrightarrow> ?thesis"
        using \<open>\<mu> x \<noteq> Var x\<close> range_vars_\<tau> mem_range_varsI[of \<tau> _ x] by auto
    qed
  qed
qed

lemma imgu_range_vars_of_equations_vars_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and Evars :: "'v set"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  defines "Evars \<equiv> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "(\<Union>x \<in> Evars. vars_term (\<mu> x)) \<subseteq> Evars"
proof (rule Set.subsetI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E" and minimal_\<mu>: "\<forall>\<tau> \<in> unifiers E. \<mu> \<circ>\<^sub>s \<tau> = \<tau>"
    by (simp_all add: is_imgu_def)

  from fin_E obtain es :: "('f, 'v) equation list" where
    "set es = E"
    using finite_list by auto
  then obtain xs :: "('v \<times> ('f, 'v) Term.term) list" where
    unify_es: "unify es [] = Some xs"
    using unif_\<mu> ex_unify_if_unifiers_not_empty by blast

  define \<tau> :: "('f, 'v) subst" where
    "\<tau> = subst_of xs"

  have dom_\<tau>: "subst_domain \<tau> \<subseteq> Evars"
    using unify_subst_domain[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  have range_vars_\<tau>: "range_vars \<tau> \<subseteq> Evars"
    using unify_range_vars[OF unify_es, unfolded \<open>set es = E\<close>, folded Evars_def \<tau>_def] .
  hence ball_vars_apply_\<tau>_subset: "\<forall>x \<in> subst_domain \<tau>. vars_term (\<tau> x) \<subseteq> Evars"
    unfolding range_vars_def
    by (simp add: SUP_le_iff)

  have "\<tau> \<in> unifiers E"
    using \<open>set es = E\<close> unify_es \<tau>_def is_imgu_def unify_sound by blast
  with minimal_\<mu> have \<mu>_comp_\<tau>: "\<And>x. (\<mu> \<circ>\<^sub>s \<tau>) x = \<tau> x"
    by auto

  fix y :: 'v assume "y \<in> (\<Union>x \<in> Evars. vars_term (\<mu> x))"
  then obtain x :: 'v where
    x_in: "x \<in> Evars" and y_in: "y \<in> vars_term (\<mu> x)"
    by (auto simp: subst_domain_def)
  have vars_\<tau>_x: "vars_term (\<tau> x) \<subseteq> Evars"
    using ball_vars_apply_\<tau>_subset subst_domain_def x_in by fastforce

  show "y \<in> Evars"
  proof (rule ccontr)
    assume "y \<notin> Evars"
    hence "y \<notin> vars_term (\<tau> x)"
      using vars_\<tau>_x by blast
    moreover have "y \<in> vars_term ((\<mu> \<circ>\<^sub>s \<tau>) x)"
    proof -
      have "\<tau> y = Var y"
        using \<open>y \<notin> Evars\<close> dom_\<tau>
        by (auto simp add: subst_domain_def)
      thus ?thesis
        unfolding subst_compose_def vars_term_subst_apply_term UN_iff
        using y_in by force
    qed
    ultimately show False
      using \<mu>_comp_\<tau>[of x] by simp
  qed
qed

lemma imgu_range_vars_subset: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  shows "range_vars \<mu> \<subseteq> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
proof -
  have "range_vars \<mu> = (\<Union>x \<in> subst_domain \<mu>. vars_term (\<mu> x))"
    by (simp add: range_vars_def)
  also have "\<dots> \<subseteq> (\<Union>x \<in> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e)). vars_term (\<mu> x))"
    using imgu_subst_domain_subset[OF imgu_\<mu> fin_E] by fast
  also have "\<dots> \<subseteq> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
    using imgu_range_vars_of_equations_vars_subset[OF imgu_\<mu> fin_E] by metis
  finally show ?thesis .
qed


definition the_mgu :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f ,'v) subst" where
  "the_mgu s t = (case mgu s t of None \<Rightarrow> Var | Some \<delta> \<Rightarrow> \<delta>)"

lemma the_mgu_is_imgu:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "s \<cdot> \<sigma> = t \<cdot> \<sigma>"
  shows "is_imgu (the_mgu s t) {(s, t)}"
proof -
  from assms have "unifiers {(s, t)} \<noteq> {}" by (force simp: unifiers_def)
  then obtain \<tau> where "mgu s t = Some \<tau>"
    and "the_mgu s t = \<tau>"
    using mgu_complete by (auto simp: the_mgu_def)
  with mgu_sound show ?thesis by blast
qed

lemma the_mgu:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "s \<cdot> \<sigma> = t \<cdot> \<sigma>"
  shows "s \<cdot> the_mgu s t = t \<cdot> the_mgu s t \<and> \<sigma> = the_mgu s t \<circ>\<^sub>s \<sigma>" 
proof -
  have *: "\<sigma> \<in> unifiers {(s, t)}" by (force simp: assms unifiers_def)
  show ?thesis
  proof (cases "mgu s t")
    assume "mgu s t = None"
    then have "unifiers {(s, t)} = {}" by (rule mgu_complete)
    with * show ?thesis by simp
  next
    fix \<tau>
    assume "mgu s t = Some \<tau>"
    moreover then have "is_imgu \<tau> {(s, t)}" by (rule mgu_sound)
    ultimately have "is_imgu (the_mgu s t) {(s, t)}" by (unfold the_mgu_def, simp)
    with * show ?thesis by (auto simp: is_imgu_def unifiers_def)
  qed
qed

subsubsection \<open>Unification of two terms where variables should be considered disjoint\<close>

definition
  mgu_var_disjoint_generic ::
    "('v \<Rightarrow> 'u) \<Rightarrow> ('w \<Rightarrow> 'u) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'w) term \<Rightarrow>
      (('f, 'v, 'u) gsubst \<times> ('f, 'w, 'u) gsubst) option"
where
  "mgu_var_disjoint_generic vu wu s t =
    (case mgu (map_vars_term vu s) (map_vars_term wu t) of
      None \<Rightarrow> None 
    | Some \<gamma> \<Rightarrow> Some (\<gamma> \<circ> vu, \<gamma> \<circ> wu))"

lemma mgu_var_disjoint_generic_sound: 
  assumes unif: "mgu_var_disjoint_generic vu wu s t = Some (\<gamma>1, \<gamma>2)"
  shows "s \<cdot> \<gamma>1 = t \<cdot> \<gamma>2"
proof -
  from unif[unfolded mgu_var_disjoint_generic_def] obtain \<gamma> where
    unif2: "mgu (map_vars_term vu s) (map_vars_term wu t) = Some \<gamma>"
    by (cases "mgu (map_vars_term vu s) (map_vars_term wu t)", auto)
  from mgu_sound[OF unif2[unfolded mgu_var_disjoint_generic_def], unfolded is_imgu_def unifiers_def]
  have "map_vars_term vu s \<cdot> \<gamma> = map_vars_term wu t \<cdot> \<gamma>" by auto
  from this[unfolded apply_subst_map_vars_term] unif[unfolded mgu_var_disjoint_generic_def unif2] 
  show ?thesis by simp
qed

(* if terms s and t can become identical via two substitutions \<sigma> and \<delta> 
   then mgu_var_disjoint yields two more general substitutions \<mu>1 \<mu>2 *)
lemma mgu_var_disjoint_generic_complete:
  fixes \<sigma> :: "('f, 'v, 'u) gsubst" and \<tau> :: "('f, 'w, 'u) gsubst" 
    and vu :: "'v \<Rightarrow> 'u" and wu:: "'w \<Rightarrow> 'u"
  assumes inj: "inj vu" "inj wu"
    and vwu: "range vu \<inter> range wu = {}"
    and unif_disj: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu>1 \<mu>2 \<delta>. mgu_var_disjoint_generic vu wu s t = Some (\<mu>1, \<mu>2) \<and> 
    \<sigma> = \<mu>1 \<circ>\<^sub>s \<delta> \<and>
    \<tau> = \<mu>2 \<circ>\<^sub>s \<delta> \<and>
    s \<cdot> \<mu>1 = t \<cdot> \<mu>2"
proof -
  note inv1[simp] = the_inv_f_f[OF inj(1)]
  note inv2[simp] = the_inv_f_f[OF inj(2)]
  obtain \<gamma> :: "('f,'u)subst" where gamma: "\<gamma> = (\<lambda> x. if x \<in> range vu then \<sigma> (the_inv vu x) else \<tau> (the_inv wu x))" by auto 
  have ids: "s \<cdot> \<sigma> = map_vars_term vu s \<cdot> \<gamma>" unfolding gamma
    by (induct s, auto)
  have idt: "t \<cdot> \<tau> = map_vars_term wu t \<cdot> \<gamma>" unfolding gamma
    by (induct t, insert vwu, auto)
  from unif_disj ids idt
  have unif: "map_vars_term vu s \<cdot> \<gamma> = map_vars_term wu t \<cdot> \<gamma>" (is "?s \<cdot> \<gamma> = ?t \<cdot> \<gamma>") by auto
  from the_mgu[OF unif] have unif2: "?s \<cdot> the_mgu ?s ?t = ?t \<cdot> the_mgu ?s ?t" and inst: "\<gamma> = the_mgu ?s ?t \<circ>\<^sub>s \<gamma>" by auto
  have "mgu ?s ?t = Some (the_mgu ?s ?t)" unfolding the_mgu_def
    using mgu_complete[unfolded unifiers_def] unif
    by (cases "mgu ?s ?t", auto)
  with inst obtain \<mu> where mu: "mgu ?s ?t = Some \<mu>" and gamma_mu: "\<gamma> = \<mu> \<circ>\<^sub>s \<gamma>" by auto
  let ?tau1 = "\<mu> \<circ> vu"
  let ?tau2 = "\<mu> \<circ> wu"
  show ?thesis unfolding mgu_var_disjoint_generic_def mu option.simps
  proof (intro exI conjI, rule refl)
    show "\<sigma> = ?tau1 \<circ>\<^sub>s \<gamma>"
    proof (rule ext)
      fix x
      have "(?tau1 \<circ>\<^sub>s \<gamma>) x = \<gamma> (vu x)" using fun_cong[OF gamma_mu, of "vu x"] by (simp add: subst_compose_def)
      also have "... = \<sigma> x" unfolding gamma by simp
      finally show "\<sigma> x = (?tau1 \<circ>\<^sub>s \<gamma>) x" by simp
    qed
  next
    show "\<tau> = ?tau2 \<circ>\<^sub>s \<gamma>"
    proof (rule ext)
      fix x
      have "(?tau2 \<circ>\<^sub>s \<gamma>) x = \<gamma> (wu x)" using fun_cong[OF gamma_mu, of "wu x"] by (simp add: subst_compose_def)
      also have "... = \<tau> x" unfolding gamma using vwu by auto
      finally show "\<tau> x = (?tau2 \<circ>\<^sub>s \<gamma>) x" by simp
    qed
  next
    have "s \<cdot> ?tau1 = map_vars_term vu s \<cdot> \<mu>" unfolding apply_subst_map_vars_term ..
    also have "... = map_vars_term wu t \<cdot> \<mu>"
      unfolding unif2[unfolded the_mgu_def mu option.simps] ..
    also have "... = t \<cdot> ?tau2" unfolding apply_subst_map_vars_term ..
    finally show "s \<cdot> ?tau1 = t \<cdot> ?tau2" .
  qed
qed

abbreviation "mgu_var_disjoint_sum \<equiv> mgu_var_disjoint_generic Inl Inr"

lemma mgu_var_disjoint_sum_sound: 
  "mgu_var_disjoint_sum s t = Some (\<gamma>1, \<gamma>2) \<Longrightarrow> s \<cdot> \<gamma>1 = t \<cdot> \<gamma>2"
  by (rule mgu_var_disjoint_generic_sound)

lemma mgu_var_disjoint_sum_complete:
  fixes \<sigma> :: "('f, 'v, 'v + 'w) gsubst" and \<tau> :: "('f, 'w, 'v + 'w) gsubst"
  assumes unif_disj: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu>1 \<mu>2 \<delta>. mgu_var_disjoint_sum s t = Some (\<mu>1, \<mu>2) \<and> 
    \<sigma> = \<mu>1 \<circ>\<^sub>s \<delta> \<and>
    \<tau> = \<mu>2 \<circ>\<^sub>s \<delta> \<and>
    s \<cdot> \<mu>1 = t \<cdot> \<mu>2"
  by (rule mgu_var_disjoint_generic_complete[OF _ _ _ unif_disj], auto simp: inj_on_def)

lemma mgu_var_disjoint_sum_instance:
  fixes \<sigma> :: "('f, 'v) subst" and \<delta> :: "('f, 'v) subst"
  assumes unif_disj: "s \<cdot> \<sigma> = t \<cdot> \<delta>"
  shows "\<exists>\<mu>1 \<mu>2 \<tau>. mgu_var_disjoint_sum s t = Some (\<mu>1, \<mu>2) \<and>
    \<sigma> = \<mu>1 \<circ>\<^sub>s \<tau> \<and>
    \<delta> = \<mu>2 \<circ>\<^sub>s \<tau> \<and> 
    s \<cdot> \<mu>1 = t \<cdot> \<mu>2"
proof -
  let ?map = "\<lambda> m \<sigma> v. map_vars_term m (\<sigma> v)"
  let ?m = "?map (Inl :: ('v \<Rightarrow> 'v + 'v))"
  let ?m' = "?map (case_sum (\<lambda> x. x) (\<lambda> x. x))"
  from unif_disj have id: "map_vars_term Inl (s \<cdot> \<sigma>) = map_vars_term Inl (t \<cdot> \<delta>)" by simp
  from mgu_var_disjoint_sum_complete[OF id[unfolded map_vars_term_subst]]
  obtain \<mu>1 \<mu>2 \<tau> where mgu: "mgu_var_disjoint_sum s t = Some (\<mu>1,\<mu>2)"
    and \<sigma>: "?m \<sigma> = \<mu>1 \<circ>\<^sub>s \<tau>" 
    and \<delta>: "?m \<delta> = \<mu>2 \<circ>\<^sub>s \<tau>"
    and unif: "s \<cdot> \<mu>1 = t \<cdot> \<mu>2" by blast
  {
    fix \<sigma> :: "('f, 'v) subst"
    have "?m' (?m \<sigma>) = \<sigma>" by (simp add: map_vars_term_compose o_def term.map_ident)
  } note id = this
  {
    fix \<mu> :: "('f,'v,'v+'v)gsubst" and \<tau> :: "('f,'v + 'v)subst"
    have "?m' (\<mu> \<circ>\<^sub>s \<tau>) = \<mu> \<circ>\<^sub>s ?m' \<tau>"
      by (rule ext, unfold subst_compose_def, simp add: map_vars_term_subst)
  } note id' = this
  from arg_cong[OF \<sigma>, of ?m', unfolded id id'] have \<sigma>: "\<sigma> = \<mu>1 \<circ>\<^sub>s ?m' \<tau>" .
  from arg_cong[OF \<delta>, of ?m', unfolded id id'] have \<delta>: "\<delta> = \<mu>2 \<circ>\<^sub>s ?m' \<tau>" .
  show ?thesis
    by (intro exI conjI, rule mgu, rule \<sigma>, rule \<delta>, rule unif)
qed

subsubsection \<open>A variable disjoint unification algorithm without changing the type\<close>

text \<open>We pass the renaming function as additional argument\<close>

definition mgu_vd :: "'v :: infinite renaming2 \<Rightarrow> _ \<Rightarrow> _" where
  "mgu_vd r = mgu_var_disjoint_generic (rename_1 r) (rename_2 r)" 

lemma mgu_vd_sound: "mgu_vd r s t = Some (\<gamma>1, \<gamma>2) \<Longrightarrow> s \<cdot> \<gamma>1 = t \<cdot> \<gamma>2"
  unfolding mgu_vd_def by (rule mgu_var_disjoint_generic_sound)

lemma mgu_vd_complete: 
  fixes \<sigma> :: "('f, 'v :: infinite) subst" and \<tau> :: "('f, 'v) subst" 
  assumes unif_disj: "s \<cdot> \<sigma> = t \<cdot> \<tau>"
  shows "\<exists>\<mu>1 \<mu>2 \<delta>. mgu_vd r s t = Some (\<mu>1, \<mu>2) \<and>
    \<sigma> = \<mu>1 \<circ>\<^sub>s \<delta> \<and>
    \<tau> = \<mu>2 \<circ>\<^sub>s \<delta> \<and>
    s \<cdot> \<mu>1 = t \<cdot> \<mu>2"
  unfolding mgu_vd_def
  by (rule mgu_var_disjoint_generic_complete[OF rename_12 unif_disj])

end
