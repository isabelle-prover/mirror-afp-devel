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
fun mgu :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst option" where
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

lemma mgu_complete:
  "mgu s t = None \<Longrightarrow> unifiers {(s, t)} = {}"
proof -
  assume "mgu s t = None"
  then have "unify [(s, t)] [] = None" by (cases "unify [(s, t)] []", auto)
  then have "unifiers (set [(s, t)]) = {}" by (rule unify_complete)
  then show ?thesis by simp
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
    using assms by (simp split: option.splits)
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
    using assms by (simp split: option.splits)
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
    using assms by (simp split: option.splits)
  thus ?thesis
    using unify_subst_domain_range_vars_disjoint by metis
qed

lemma mgu_sound:
  assumes "mgu s t = Some \<sigma>"
  shows "is_imgu \<sigma> {(s, t)}"
proof -
  obtain ss where "unify [(s, t)] [] = Some ss"
    and "\<sigma> = subst_of ss"
    using assms by (auto split: option.splits)
  then have "is_imgu \<sigma> (set [(s, t)])" by (metis unify_sound)
  then show ?thesis by simp
qed

corollary subst_apply_term_eq_subst_apply_term_if_mgu: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  assumes mgu_t_u: "mgu t u = Some \<mu>"
  shows "t \<cdot> \<mu> = u \<cdot> \<mu>"
  using mgu_sound[OF mgu_t_u]
  by (simp add: is_imgu_def unifiers_def)

lemma mgu_same: "mgu t t = Some Var" \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  by (simp add: unify_same)

lemma ex_mgu_if_subst_apply_term_eq_subst_apply_term: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes t u :: "('f, 'v) Term.term" and \<sigma> :: "('f, 'v) subst"
  assumes t_eq_u: "t \<cdot> \<sigma> = u \<cdot> \<sigma>"
  shows "\<exists>\<mu> :: ('f, 'v) subst. Unification.mgu t u = Some \<mu>"
proof -
  from t_eq_u have "unifiers {(t, u)} \<noteq> {}"
    unfolding unifiers_def by auto
  then obtain xs where unify: "unify [(t, u)] [] = Some xs"
    using unify_complete
    by (metis list.set(1) list.set(2) not_Some_eq)

  show ?thesis
  proof (rule exI)
    show "Unification.mgu t u = Some (subst_of xs)"
      using unify by simp
  qed
qed

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

end
