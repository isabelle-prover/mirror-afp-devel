section \<open>First map\<close>

theory First_Map
imports Nullable_Set "HOL-Library.Finite_Map"
begin

type_synonym ('n, 't) first_map = "('n, 't lookahead list) fmap"

fun nullableSym :: "('n, 't) symbol \<Rightarrow> 'n set \<Rightarrow> bool" where
  "nullableSym (T _) _ = False"
| "nullableSym (NT x) nu = (x \<in> nu)"

definition findOrEmpty :: "'n \<Rightarrow> ('n, 't) first_map \<Rightarrow> 't lookahead list" where
  "findOrEmpty x m = (case fmlookup m x of None \<Rightarrow> [] | Some y \<Rightarrow> y)"

fun firstSym :: "('n, 't) symbol \<Rightarrow> ('n, 't) first_map \<Rightarrow> 't lookahead list" where
  "firstSym (T x) _ = [LA x]"
| "firstSym (NT x) fi = findOrEmpty x fi"


definition list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@@" 65) where
  "list_union ls1 ls2 = ls1 @ (filter (\<lambda>x. x \<notin> set ls1) ls2)"

lemma in_atleast1_list: "a \<in> set (ls1 @@ ls2) \<Longrightarrow> a \<in> set ls1 \<or> a \<in> set ls2"
  unfolding list_union_def
  by auto

lemma set_list_union[simp]: "set (ls1 @@ ls2) = set ls1 \<union> set ls2"
  unfolding list_union_def
  by auto

lemma mem_list_union: "ls1 = ls1 @@ ls2 \<Longrightarrow> e \<in> set ls2 \<Longrightarrow> e \<in> set ls1"
  by (metis Un_iff set_list_union)

lemma list_union_I2: "e \<in> set ls2 \<Longrightarrow> e \<in> set (ls1 @@ ls2)"
  by simp

fun firstGamma :: "('n, 't) rhs \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> 't lookahead list" where
  "firstGamma [] _ _ = []"
| "firstGamma (s#gamma') nu fi =
    (if nullableSym s nu then firstSym s fi @@ firstGamma gamma' nu fi else firstSym s fi)"

definition updateFi :: "'n set \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) first_map" where
  "updateFi \<equiv> \<lambda>nu (x, gamma) fi. (let
    fg = firstGamma gamma nu fi;
    xFirst = findOrEmpty x fi;
    xFirst' = xFirst @@ fg in (if xFirst' = xFirst \<or> fg = [] then fi else fmupd x xFirst' fi))"

definition firstPass :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) first_map" where
  "firstPass ps nu fi = foldr (updateFi nu) ps fi"

partial_function (option) mkFirstMap' :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map
    \<Rightarrow> ('n, 't) first_map option" where
  "mkFirstMap' ps nu fi = (let fi' = firstPass ps nu fi in
    (if fi = fi' then Some fi else mkFirstMap' ps nu fi'))"

definition mkFirstMap :: "('n, 't) grammar \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map" where
  "mkFirstMap g nu = the (mkFirstMap' (prods g) nu fmempty)"


subsection \<open>Termination\<close>

fun leftmostLookahead :: "('n, 't) rhs \<Rightarrow> 't lookahead option" where
  "leftmostLookahead [] = None"
| "leftmostLookahead ((T y)#gamma') = Some (LA y)"
| "leftmostLookahead ((NT _)#gamma') = leftmostLookahead gamma'"

definition leftmostLookaheads :: "('n, 't) prods \<Rightarrow> 't lookahead set" where
  "leftmostLookaheads ps = the ` leftmostLookahead ` snd ` set ps"

lemma in_leftmostLookaheads_cons: "x \<in> leftmostLookaheads ps \<Longrightarrow> x \<in> leftmostLookaheads (p # ps)"
  unfolding leftmostLookaheads_def by auto

definition pairsOf :: "('n, 't) first_map \<Rightarrow> ('n \<times> 't lookahead) set" where
  "pairsOf fi = {(a, b). a |\<in>| fmdom fi \<and> b \<in> set (findOrEmpty a fi)}"

definition all_nt :: "('n, 't) rhs \<Rightarrow> bool" where
  "all_nt gamma = (\<forall>s \<in> set gamma. (case s of (NT _) \<Rightarrow> True | (T _) \<Rightarrow> False))"

definition all_pairs_are_first_candidates:: "('n, 't) first_map \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where
  "all_pairs_are_first_candidates fi ps =
  (\<forall>x la. (x, la) \<in> pairsOf fi \<longrightarrow> (x \<in> lhSet ps \<and> la \<in> leftmostLookaheads ps))"

definition countFirstCands :: "('n, 't) prods \<Rightarrow> ('n, 't) first_map \<Rightarrow> nat" where
  "countFirstCands ps fi = (let allCandidates = (lhSet ps) \<times> (leftmostLookaheads ps) in
    card (allCandidates - (pairsOf fi)))"

lemma gpre_nullable_leftmost_lk_some: "all_nt gpre
    \<Longrightarrow> leftmostLookahead (gpre @ (T y) # gsuf) = Some (LA y)"
  by (induction gpre) (auto simp: all_nt_def split: symbol.splits)

lemma gpre_nullable_in_leftmost_lks:
  "(x, (gpre @ (T y) # gsuf)) \<in> set ps \<Longrightarrow> all_nt gpre \<Longrightarrow> (LA y) \<in> leftmostLookaheads ps"
proof (induction ps)
  case Nil
  then show ?case by auto
next
  case (Cons p ps')
  then show ?case
  proof (cases "p = (x, gpre @ (T y) # gsuf)")
    case True
    then show ?thesis unfolding leftmostLookaheads_def
      using Cons.prems(2) gpre_nullable_leftmost_lk_some by fastforce
  next
    case False
    then show ?thesis using Cons by (auto simp add: in_leftmostLookaheads_cons)
  qed
qed

lemma in_firstGamma_in_leftmost_lks':
  assumes "(x, gpre @ gsuf) \<in> set ps" "all_pairs_are_first_candidates fi ps" "all_nt gpre"
  shows "la \<in> set (firstGamma gsuf nu fi) \<Longrightarrow> la \<in> leftmostLookaheads ps"
  using assms
proof (induction gsuf arbitrary: gpre)
  case Nil
  then show ?case by auto
next
  case (Cons y gsuf)
  consider (T) a where "y = T a" | (NT_nullable) a where "y = NT a" and "nullableSym y nu"
    | (NT_not_nullable)  a where "y = NT a" and "\<not> nullableSym y nu" by (cases y; auto)
  then show ?case
  proof cases
    case T
    then show ?thesis using Cons.prems by (auto intro: gpre_nullable_in_leftmost_lks)
  next
    case (NT_nullable a)
    then consider (in_findOrEmpty) "la \<in> set (findOrEmpty a fi)"
      | (in_firstGamma) "la \<in> set (firstGamma gsuf nu fi)"
      using Cons.prems(1) by fastforce
    then show ?thesis
    proof cases
      case in_findOrEmpty
      then have "(a, la) \<in> pairsOf fi" unfolding findOrEmpty_def
        using fmdom_notD in_findOrEmpty pairsOf_def by fastforce
      then show ?thesis using Cons.prems(3) unfolding all_pairs_are_first_candidates_def by auto
    next
      case in_firstGamma
      then show ?thesis using Cons.prems(2,3,4) by
        (auto intro: Cons.IH[of "gpre @ [y]"] simp add: all_nt_def NT_nullable)
    qed
  next
    case NT_not_nullable
    then have "(a, la) \<in> pairsOf fi" using Cons.prems(1) unfolding pairsOf_def by
      (cases "fmlookup fi a"; auto intro: fmdomI simp add: NT_not_nullable findOrEmpty_def)
    then show ?thesis using Cons.prems(3) unfolding all_pairs_are_first_candidates_def by auto
  qed
qed

lemma in_firstGamma_in_leftmost_lks: "(x, gamma) \<in> set ps \<Longrightarrow> all_pairs_are_first_candidates fi ps
  \<Longrightarrow> la \<in> set (firstGamma gamma nu fi) \<Longrightarrow> la \<in> leftmostLookaheads ps"
  by (auto intro: in_firstGamma_in_leftmost_lks'[of x "[]" gamma] simp add: all_nt_def)

lemma updateFi_cases:
  fixes nu and x :: 'n and gamma :: "('n, 't) rhs" and fi
  defines "fg \<equiv> firstGamma gamma nu fi"
  defines "xFirst \<equiv> findOrEmpty x fi"
  defines "xFirst' \<equiv> xFirst @@ fg"
  obtains (unchanged) "xFirst' = xFirst" "updateFi nu (x, gamma) fi = fi"
  | (empty) "fg = []" "updateFi nu (x, gamma) fi = fi"
  | (new) la where "xFirst' \<noteq> xFirst \<Longrightarrow> la \<in> set fg \<Longrightarrow> la \<notin> set xFirst
      \<Longrightarrow> updateFi nu (x, gamma) fi = fmupd x xFirst' fi"
  unfolding updateFi_def fg_def[symmetric] xFirst_def[symmetric] xFirst'_def[symmetric]
  by atomize_elim (auto split: if_split_asm simp: Let_def xFirst'_def fg_def xFirst_def)

lemma firstPass_induct:
  fixes ps :: "('n, 't) prods"
    and nu :: "'n set"
    and fi :: "('n, 't) first_map"
    and P :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> bool"
  assumes Nil: "P [] nu fi"
    and Cons_changed: "\<And>p ps'. (P ps' nu fi \<Longrightarrow> fi \<noteq> firstPass ps' nu fi \<Longrightarrow> P (p # ps') nu fi)"
    and Cons_same: "\<And>p ps'. (P ps' nu fi \<Longrightarrow> fi = firstPass ps' nu fi \<Longrightarrow> P (p # ps') nu fi)"
  shows "P (ps :: ('n, 't) prods) nu fi"
  using Nil Cons_changed Cons_same
  by -(rule list.induct[where ?P = "\<lambda>ls. P ls nu fi"]; blast)

lemma in_findOrEmpty_iff_in_pairsOf: "la \<in> set (findOrEmpty x fi) \<longleftrightarrow> (x, la) \<in> pairsOf fi"
  unfolding findOrEmpty_def pairsOf_def using fmdom_notD by fastforce

lemma in_pairsOf_exists: "(x, la) \<in> pairsOf fi \<longleftrightarrow> (\<exists>s. fmlookup fi x = Some s \<and> la \<in> set s)"
  unfolding pairsOf_def findOrEmpty_def using fmlookup_dom_iff by fastforce

lemma in_findOrEmpty_exists_set:
    "la \<in> set (findOrEmpty x m) \<longleftrightarrow> (\<exists>s. fmlookup m x = Some s \<and> la \<in> set s)"
  using in_findOrEmpty_iff_in_pairsOf in_pairsOf_exists by fast

lemma in_add_value: "(x, la) \<in> pairsOf (fmupd x s fi) \<longleftrightarrow> la \<in> set s"
  by (simp add: in_pairsOf_exists)

lemma firstPass_Nil[simp]: "firstPass [] x y = y"
  unfolding firstPass_def by simp

text\<open>Lemma for the simplification of \<^term>\<open>firstPass\<close>.
In general, one function call should be unfolded
instead of replacing it with its definition with \<^term>\<open>foldr\<close>.\<close>

lemma firstPass_cons[simp]: "firstPass (a # ps) nu fi = updateFi nu a (firstPass ps nu fi)"
  by (simp add: firstPass_def)

lemma unfold_updateFi: "updateFi nu (x, gamma) fi =
  (if findOrEmpty x fi @@ firstGamma gamma nu fi = findOrEmpty x fi
    \<or> findOrEmpty x fi @@ firstGamma gamma nu fi = []
  then fi else fmupd x (findOrEmpty x fi @@ firstGamma gamma nu fi) fi)"
  by (auto simp add: updateFi_def Let_def list_union_def)

lemma in_add_keys: "la \<in> set s \<longleftrightarrow> (x, la) \<in> pairsOf (fmupd x s fi)"
  by (simp add: in_findOrEmpty_iff_in_pairsOf[symmetric] findOrEmpty_def)

lemma in_add_keys_neq: "x \<noteq> y \<Longrightarrow> (y, la) \<in> pairsOf fi \<longleftrightarrow> (y, la) \<in> pairsOf (fmupd x s fi)"
  by (simp add: findOrEmpty_def pairsOf_def)


lemma updateFi_subset: "pairsOf fi \<subseteq> pairsOf (updateFi nu p fi)"
proof (rule subrelI)
  fix y la
  assume A: "(y, la) \<in> pairsOf fi"
  obtain x gamma where p_def: "p = (x, gamma)" by (cases p)
  then consider "updateFi nu (x, gamma) fi = fi"
    | "x = y" "updateFi nu (x, gamma) fi = fmupd x (findOrEmpty x fi @@ firstGamma gamma nu fi) fi"
    | "x \<noteq> y" "updateFi nu (x, gamma) fi = fmupd x (findOrEmpty x fi @@ firstGamma gamma nu fi) fi"
    using unfold_updateFi by metis
  then show "(y, la) \<in> pairsOf (updateFi nu p fi)"
  proof (cases)
    case 1
    then show ?thesis using p_def A by simp
  next
    case 2
    then show ?thesis
      by (simp add: A in_add_value in_findOrEmpty_iff_in_pairsOf p_def list_union_def)
  next
    case 3
    then show ?thesis
      by (metis A in_add_keys_neq p_def)
  qed
qed

lemma firstPass_cons_subset: "pairsOf (firstPass ps nu fi) \<subseteq> pairsOf (firstPass (p # ps) nu fi)"
  using updateFi_subset by (cases p, simp, blast)

lemma firstPass_mono: "pairsOf (firstPass ps nu fi) \<subseteq> pairsOf (firstPass (qs @ ps) nu fi)"
  by (induction qs arbitrary: ps) (simp, metis append_Cons firstPass_cons_subset subsetD subsetI)

lemma firstPass_subset: "pairsOf fi \<subseteq> pairsOf (firstPass ps nu fi)"
  using firstPass_cons_subset by (induction ps; simp add: firstPass_def; blast)

lemma firstPass_empty_set:
  "fmlookup (firstPass ps nu fi) x = Some [] \<Longrightarrow> fmlookup fi x = Some []"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case using Cons by (cases p) (auto simp add: unfold_updateFi split: if_split_asm)
qed

lemma firstPass_None: "fmlookup (firstPass ps nu fi) x = None \<Longrightarrow> fmlookup fi x = None"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case using Cons by (cases p) (auto simp add: unfold_updateFi split: if_split_asm)
qed

lemma firstPass_neq_findOrEmpty:
  assumes "fmlookup fi x \<noteq> fmlookup (firstPass ps nu fi) x"
  shows "findOrEmpty x fi \<noteq> findOrEmpty x (firstPass ps nu fi)"
proof (cases "fmlookup (firstPass ps nu fi) x")
  case None
  then have "fmlookup fi x = None" by (auto intro: firstPass_None)
  then show ?thesis using None assms by auto
next
  case (Some xSet)
  then have "xSet \<noteq> []" using firstPass_empty_set assms by fastforce
  then show ?thesis
    using assms
    by (auto simp add: Some findOrEmpty_def split: option.splits)
qed

text\<open>Injectivity of \<^term>\<open>pairsOf\<close>\<close>

lemma firstPass_only_appends: "\<exists>suf. findOrEmpty x (firstPass ps nu fi) = findOrEmpty x fi @ suf"
  unfolding firstPass_def
proof (induction ps)
  case Nil
  then show ?case by auto
next
  case (Cons p ps)
  obtain y gamma where p_def: "p = (y, gamma)" by (cases p)
  let ?fg = "firstGamma gamma nu (foldr (updateFi nu) ps fi)"
  let ?xFirst = "findOrEmpty y (foldr (updateFi nu) ps fi)"
  let ?xFirst' = "?xFirst @@ ?fg"
  show ?case
  proof (cases "?xFirst' = ?xFirst \<or> ?fg = []")
    case True
    then show ?thesis using p_def Cons by (auto simp add: updateFi_def)
  next
    case False
    note outerFalse = this
    have "findOrEmpty x (foldr (updateFi nu) (p # ps) fi)
        = findOrEmpty x (fmupd y ?xFirst' (foldr (updateFi nu) ps fi))"
      using p_def False by (auto simp add: updateFi_def)
    then show ?thesis using Cons by (cases "x = y") (auto simp add: list_union_def findOrEmpty_def)
  qed
qed

lemma firstPass_suf_distinct: "findOrEmpty x (firstPass ps nu fi) = findOrEmpty x fi @ suf
  \<Longrightarrow> suf \<noteq> [] \<Longrightarrow> la \<in> set suf \<Longrightarrow> la \<notin> set (findOrEmpty x fi)"
proof (induction ps arbitrary: x fi suf)
  case Nil
  then show ?case by auto
next
  case (Cons p ps)
  obtain y gamma where p_def: "p = (y, gamma)" by (cases p)
  let ?fg = "firstGamma gamma nu (foldr (updateFi nu) ps fi)"
  let ?xFirst = "findOrEmpty y (foldr (updateFi nu) ps fi)"
  let ?xFirst' = "?xFirst @@ ?fg"
  show ?case
  proof (cases "?xFirst' = ?xFirst \<or> ?fg = []")
    case True
    then show ?thesis
      using Cons.IH Cons.prems(1-3) p_def
      by (simp add: firstPass_def updateFi_def)
  next
    case False
    obtain suf' where suf'_def: "findOrEmpty x (firstPass ps nu fi) = findOrEmpty x fi @ suf'"
      by (meson firstPass_only_appends)
    then show ?thesis
      proof (cases "x = y")
        case True
        then have "findOrEmpty x (firstPass (p # ps) nu fi) = ?xFirst'"
          using False p_def
          by (simp add: findOrEmpty_def firstPass_def updateFi_def)
        then have "findOrEmpty x fi @ suf
            = (findOrEmpty x fi @ suf') @@ firstGamma gamma nu (firstPass ps nu fi)"
          using Cons.prems(1) suf'_def True
          by (auto simp add: firstPass_def)
        then show ?thesis unfolding list_union_def using Cons suf'_def by force
      next
        case False
        then have "findOrEmpty x (firstPass (p # ps) nu fi) = findOrEmpty x (firstPass ps nu fi)"
          using p_def by (auto simp add: findOrEmpty_def updateFi_def Let_def)
        then show ?thesis using Cons by auto
      qed
  qed
qed

lemma pairsOf_inj: "fi \<noteq> firstPass ps nu fi \<Longrightarrow> pairsOf fi \<noteq> pairsOf (firstPass ps nu fi)"
proof -
  assume "fi \<noteq> firstPass ps nu fi"
  then obtain y where y_diff: "findOrEmpty y fi \<noteq> findOrEmpty y (firstPass ps nu fi)"
    using firstPass_neq_findOrEmpty
    by (metis fmap_ext)
  obtain suf where suf_def: "findOrEmpty y (firstPass ps nu fi) = findOrEmpty y fi @ suf"
      and "suf \<noteq> []"
    using firstPass_only_appends y_diff by force
  then obtain la where "la \<in> set suf" and "la \<notin> set (findOrEmpty y fi)"
    by (meson firstPass_suf_distinct last_in_set suf_def)
  then show ?thesis
    using in_findOrEmpty_iff_in_pairsOf suf_def
    by fastforce
qed

lemma firstPass_not_equiv_subset:
  "fi \<noteq> firstPass ps nu fi \<Longrightarrow> pairsOf fi \<subset> pairsOf (firstPass ps nu fi)"
  using pairsOf_inj firstPass_subset by blast

lemma firstPass_subset_lhs_lks: "all_pairs_are_first_candidates (firstPass ps nu fi) ps
  \<Longrightarrow> pairsOf (firstPass ps nu fi) \<subseteq> lhSet ps \<times> leftmostLookaheads ps \<union> pairsOf fi"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain x gamma where "p = (x, gamma)" by fastforce
  from Cons.prems have "all_pairs_are_first_candidates (firstPass ps nu fi) (p # ps)"
    unfolding all_pairs_are_first_candidates_def using firstPass_cons_subset by blast
  then have "set (firstGamma gamma nu (firstPass ps nu fi)) \<subseteq> leftmostLookaheads (p # ps)"
    by (auto intro: in_firstGamma_in_leftmost_lks simp add: \<open>p = (x, gamma)\<close>)
  then show ?case using Cons.prems all_pairs_are_first_candidates_def by fastforce
qed

lemma finite_leftmostLookaheads: "finite (leftmostLookaheads ps)"
  unfolding leftmostLookaheads_def by auto

lemma firstPass_not_equiv_candidates_lt: "all_pairs_are_first_candidates (firstPass ps nu fi) ps
  \<Longrightarrow> fi \<noteq> (firstPass ps nu fi)
  \<Longrightarrow> countFirstCands ps (firstPass ps nu fi) < countFirstCands ps fi"
proof -
  assume A1: "all_pairs_are_first_candidates (firstPass ps nu fi) ps"
    and A2: "fi \<noteq> (firstPass ps nu fi)"
  have "finite (lhSet ps \<times> leftmostLookaheads ps)"
    by (simp add: finite_leftmostLookaheads lhSet_def)
  moreover have "lhSet ps \<times> leftmostLookaheads ps - pairsOf (firstPass ps nu fi)
      \<subset> lhSet ps \<times> leftmostLookaheads ps - pairsOf fi"
    using firstPass_not_equiv_subset firstPass_subset_lhs_lks A1 A2 by fastforce
  ultimately have "card (lhSet ps \<times> leftmostLookaheads ps - pairsOf (firstPass ps nu fi))
    < card (lhSet ps \<times> leftmostLookaheads ps - pairsOf fi)"
    by (auto intro: psubset_card_mono)
  then show "countFirstCands ps (firstPass ps nu fi) < countFirstCands ps fi"
    unfolding countFirstCands_def by simp
qed

lemma firstPass_preserves_apac': "all_pairs_are_first_candidates fi (ps1 @ ps2)
  \<Longrightarrow> all_pairs_are_first_candidates (firstPass ps2 nu fi) (ps1 @ ps2)"
proof (induction ps2 arbitrary: ps1)
  case Nil
  then show ?case unfolding all_pairs_are_first_candidates_def by (simp add: firstPass_def)
next
  case (Cons p ps2')
  obtain x gamma where p_def: "p = (x, gamma)" by fastforce
  then show ?case using Cons.IH[of "ps1 @ [p]"] Cons.prems
  proof (cases rule:
      updateFi_cases[where x = x and nu = nu and gamma = gamma and fi = "firstPass ps2' nu fi"])
    case (new la)
    then have "x' \<in> lhSet (ps1 @ p # ps2') \<and> la' \<in> leftmostLookaheads (ps1 @ p # ps2')"
      if "(x', la') \<in> pairsOf (firstPass (p # ps2') nu fi)" for x' la'
    proof -
      from that consider "x = x'" and "la' \<in> set (findOrEmpty x (firstPass ps2' nu fi))"
        | "x = x'" and "la' \<in> set (firstGamma gamma nu (firstPass ps2' nu fi))"
        | "(x', la') \<in> pairsOf (firstPass ps2' nu fi)"
        unfolding p_def
        using firstPass_cons[of "(x, gamma)" ps2' nu fi] unfold_updateFi[of nu x gamma]
          in_add_keys in_add_keys_neq in_atleast1_list
        by metis
      then show ?thesis using Cons.prems Cons.IH[of "ps1 @ [p]"]
        by (cases, auto intro: in_firstGamma_in_leftmost_lks
          simp: lhSet_def p_def all_pairs_are_first_candidates_def in_findOrEmpty_iff_in_pairsOf)
    qed
    then show ?thesis by (simp add: all_pairs_are_first_candidates_def)
  qed (auto simp add: p_def)
qed

lemma firstPass_preserves_apac:
  "all_pairs_are_first_candidates fi ps \<Longrightarrow> all_pairs_are_first_candidates (firstPass ps nu fi) ps"
  using firstPass_preserves_apac'[of fi "[]" ps] by auto

text\<open>Termination proof for \<^term>\<open>mkFirstMap'\<close> given that \<^term>\<open>all_pairs_are_first_candidates\<close>
holds for the first call and therefore also for every following iteration.\<close>

lemma mkFirstMap'_dom_if_apac:
  "mkFirstMap' ps nu fi \<noteq> None" if "all_pairs_are_first_candidates fi ps"
  using that
proof (induction "(ps, nu, fi)" arbitrary: fi
    rule: measure_induct_rule[where f = "\<lambda>(ps, nu, fi). countFirstCands ps fi"])
  case (less fi)
  have "fi \<noteq> firstPass ps nu fi \<Longrightarrow> countFirstCands ps (firstPass ps nu fi) < countFirstCands ps fi"
    using less.prems by (simp add: firstPass_not_equiv_candidates_lt firstPass_preserves_apac)
  moreover have "fi \<noteq> firstPass ps nu fi \<Longrightarrow> all_pairs_are_first_candidates (firstPass ps nu fi) ps"
    using less.prems by (rule firstPass_preserves_apac)
  ultimately have F: "fi \<noteq> firstPass ps nu fi \<Longrightarrow> mkFirstMap' ps nu (firstPass ps nu fi) \<noteq> None" by
    (simp add: less.hyps)
  then show ?case
  proof (cases "fi \<noteq> firstPass ps nu fi")
    case True
    then show ?thesis using F by (simp add: mkFirstMap'.simps[of ps nu fi])
  next
    case False
    then show ?thesis by (simp add: mkFirstMap'.simps[of ps nu fi])
  qed
qed

lemma empty_fi_apac: "all_pairs_are_first_candidates fmempty ps"
  unfolding all_pairs_are_first_candidates_def pairsOf_def by auto

lemma mkFirstMap_simp: "mkFirstMap g nu \<equiv> (let fi' = firstPass (prods g) nu fmempty in
    (if fmempty = fi' then fmempty else the (mkFirstMap' (prods g) nu fi')))"
  unfolding mkFirstMap_def
  by (smt (verit, del_insts) mkFirstMap'.simps option.sel)


subsection \<open>Correctness Definitions\<close>

definition first_map_sound :: "('n, 't) first_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "first_map_sound fi g =
  (\<forall>x la xFirst. fmlookup fi x = Some xFirst \<and> la \<in> set xFirst \<longrightarrow> first_sym g la (NT x))"

definition first_map_complete :: "('n, 't) first_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "first_map_complete fi g = (\<forall>la s x. first_sym g la s
    \<and> s = (NT x) \<longrightarrow> (\<exists>xFirst. fmlookup fi x = Some xFirst \<and> la \<in> set xFirst))"

abbreviation first_map_for :: "('n, 't) first_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "first_map_for fi g \<equiv> first_map_sound fi g \<and> first_map_complete fi g"


subsection \<open>Soundness\<close>

lemma firstSym_first_sym: assumes "first_map_sound fi g" and "la \<in> set (firstSym s fi)"
  shows "first_sym g la s"
proof (cases s)
  case (NT x)
  then show ?thesis using assms first_map_sound_def in_findOrEmpty_exists_set by fastforce
next
  case (T x)
  then show ?thesis using assms(2) FirstT by fastforce
qed

lemma nullable_app: "nullable_gamma g xs \<Longrightarrow> nullable_gamma g ys \<Longrightarrow> nullable_gamma g (xs @ ys)"
  by (induction xs; force elim: nullable_gamma.cases intro: NullableCons)

lemma nullableSym_nullable_sym: assumes "nullable_set_for nu g"
  shows "nullableSym s nu \<longleftrightarrow> nullable_sym g s"
proof (cases s)
  case (NT x1)
  then show ?thesis using assms nullable_set_sound_def nullable_set_complete_def by fastforce
next
  case (T x2)
  then show ?thesis by (simp add: nullable_sym.simps)
qed

lemma firstGamma_first_sym': "nullable_set_for nu g \<Longrightarrow> first_map_sound fi g
  \<Longrightarrow> (x, gpre @ gsuf) \<in> set (prods g) \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> la \<in> set (firstGamma gsuf nu fi) \<Longrightarrow> first_sym g la (NT x)"
proof (induction gsuf arbitrary: gpre)
  case Nil
  then show ?case by auto
next
  case (Cons s syms)
  then show ?case
  proof (cases "nullableSym s nu")
    case True
    consider (la_in_firstSym) "la \<in> set (firstSym s fi)"
      | (la_in_firstGamma) "la \<in> set (firstGamma syms nu fi)"
      using Cons.prems(5) True by auto
    then show ?thesis
    proof (cases)
      case la_in_firstSym
      then show ?thesis using Cons.prems(2,3,4) FirstNT firstSym_first_sym by fast
    next
      case la_in_firstGamma
      have "(x, (gpre @ [s]) @ syms) \<in> set (prods g)" using Cons.prems(3) by auto
      moreover have "nullable_gamma g (gpre @ [s])"
      proof (rule nullable_app)
        show "nullable_gamma g gpre" by (simp add: Cons.prems(4))
      next
        have "nullable_sym g s" using Cons.prems(1) True nullableSym_nullable_sym by auto
        then show "nullable_gamma g [s]" by - (rule NullableCons, auto simp add: NullableNil)
      qed
      moreover have "la \<in> set (firstGamma syms nu fi)" by (simp add: la_in_firstGamma)
      ultimately show ?thesis using Cons.prems(1,2) by - (rule Cons.IH[where gpre = "gpre @ [s]"])
    qed
  next
    case False
    then show ?thesis using firstSym_first_sym Cons.prems(2,3,4,5) FirstNT by fastforce
  qed
qed

lemma firstGamma_first_sym: "nullable_set_for nu g \<Longrightarrow> first_map_sound fi g
    \<Longrightarrow> (x, gamma) \<in> set (prods g) \<Longrightarrow> la \<in> set (firstGamma gamma nu fi) \<Longrightarrow> first_sym g la (NT x)"
  using NullableNil append.left_neutral firstGamma_first_sym' by force

lemma firstPass_preserves_soundness': "nullable_set_for nu g \<Longrightarrow> first_map_sound fi g
  \<Longrightarrow> set ps \<subseteq> set (prods g) \<Longrightarrow> first_map_sound (firstPass ps nu fi) g"
proof (induction ps)
  case Nil
  then show ?case by (simp add: firstPass_def)
next
  case (Cons a suf)
  obtain x gamma where "a = (x, gamma)" by fastforce
  let ?fi' = "firstPass suf nu fi"
  let ?fg = "firstGamma gamma nu ?fi'"
  let ?xFirst = "findOrEmpty x ?fi'"
  let ?xFirst' = "?xFirst @@ ?fg"
  have fi'_sound: "first_map_sound ?fi' g" using Cons by auto
  show ?case
  proof (cases "?xFirst = ?xFirst'")
    case True
    then show ?thesis using \<open>a = (x, gamma)\<close> True fi'_sound by (auto simp add: unfold_updateFi)
  next
    case False
    have "fmlookup (fmupd x (?xFirst @@ ?xFirst') ?fi') y = Some yFirst  \<Longrightarrow> la \<in> set yFirst
        \<Longrightarrow> first_sym g la (NT y)" for y yFirst la
    proof (cases "x = y")
      case True
      assume "fmlookup (fmupd x (?xFirst @@ ?xFirst') ?fi') y = Some yFirst" "la \<in> set yFirst"
      then consider (la_in_xFirst) "la \<in> set ?xFirst" | (la_in_fg) "la \<in> set ?fg"
        using \<open>la \<in> set yFirst\<close> True
        by auto
      then show ?thesis
      proof (cases)
        case la_in_xFirst
        then have "la \<in> set (firstSym (NT y) ?fi')" using True by auto
        then show ?thesis by - (rule firstSym_first_sym, auto simp add: fi'_sound)
      next
        case la_in_fg
        have "(y, gamma) \<in> set (prods g)" using Cons.prems(3) True \<open>a = (x, gamma)\<close> by auto
      then show ?thesis using fi'_sound Cons.prems(1) la_in_fg by
        - (rule firstGamma_first_sym[of nu g ?fi' y gamma], auto)
      qed
    next
      case False
      assume "fmlookup (fmupd x (?xFirst @@ ?xFirst') ?fi') y = Some yFirst" "la \<in> set yFirst"
      then have "fmlookup ?fi' y = Some yFirst" by (simp add: False)
      then show ?thesis using \<open>la \<in> set yFirst\<close> fi'_sound first_map_sound_def by fastforce
    qed
    then have "first_map_sound (fmupd x ?xFirst' ?fi') g" unfolding first_map_sound_def by auto
    then show ?thesis using \<open>a = (x, gamma)\<close> False fi'_sound by (auto simp add: unfold_updateFi)
  qed
qed

lemma firstPass_preserves_soundness: "nullable_set_for nu g \<Longrightarrow> first_map_sound fi g
    \<Longrightarrow> first_map_sound (firstPass (prods g) nu fi) g"
  by (simp add: firstPass_preserves_soundness')

lemma mkFirstMap'_preserves_soundness: "nullable_set_for nu g \<Longrightarrow> first_map_sound fi g
  \<Longrightarrow> all_pairs_are_first_candidates fi (prods g)
  \<Longrightarrow> first_map_sound (the (mkFirstMap' (prods g) nu fi)) g"
proof (induction "countFirstCands (prods g) fi" arbitrary: fi rule: less_induct)
  case less
  let ?fi' = "firstPass (prods g) nu fi"
  obtain fi'' where fi''_def: "mkFirstMap' (prods g) nu ?fi' = Some fi''"
    using firstPass_preserves_apac[of fi "prods g" nu] less.prems(3)
      mkFirstMap'_dom_if_apac[of "firstPass (prods g) nu fi"] by auto
  moreover have "first_map_sound (if fi = ?fi' then fi else fi'') g"
  proof (cases "fi = ?fi'")
    case True
    then show ?thesis using less.prems(2) by auto
  next
    case False
    have "countFirstCands (prods g) ?fi' < countFirstCands (prods g) fi" using less.prems(3) False
      by (simp add: firstPass_not_equiv_candidates_lt firstPass_preserves_apac)
    moreover have "first_map_sound ?fi' g" using less.prems by
      - (rule firstPass_preserves_soundness, auto)
    ultimately show ?thesis using firstPass_preserves_apac less fi''_def by fastforce
  qed
  ultimately show ?case by (auto simp add: mkFirstMap'.simps Let_def)
qed

lemma empty_fi_sound: "first_map_sound fmempty g"
  unfolding first_map_sound_def by auto

theorem mkFirstMap_sound: "nullable_set_for nu g \<Longrightarrow> first_map_sound (mkFirstMap g nu) g"
  unfolding mkFirstMap_def
  by (simp add: empty_fi_sound mkFirstMap'_preserves_soundness empty_fi_apac)


subsection \<open>Completeness\<close>

lemma la_in_firstGamma_t: "nullable_set_for nu g \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> LA y \<in> set (firstGamma (gpre @ T y # gsuf) nu fi)"
proof (induction gpre)
  case Nil
  then show ?case by simp
next
  case (Cons s gpre)
  from Cons.prems(2) have "nullable_sym g s" by (cases) auto
  then have "nullableSym s nu" using Cons.prems(1) nullableSym_nullable_sym by blast
  from Cons.prems(2) have "nullable_gamma g gpre" by (cases) simp
  then have "LA y \<in> set (firstGamma (gpre @ T y # gsuf) nu fi)" using Cons.IH Cons.prems(1) by auto
  then show ?case using \<open>nullableSym s nu\<close> by auto
qed

lemma la_in_firstGamma_nt: "nullable_set_for nu g \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> fmlookup fi x = Some xFirst \<Longrightarrow> la \<in> set xFirst
  \<Longrightarrow> la \<in> set (firstGamma (gpre @ NT x # gsuf) nu fi)"
proof (induction gpre)
  case Nil
  then show ?case by (simp add: findOrEmpty_def)
next
  case (Cons s gpre)
  from Cons.prems(2) have "nullable_sym g s" by (cases) auto
  then have "nullableSym s nu" using Cons.prems(1) nullableSym_nullable_sym by blast
  from Cons.prems(2) have "nullable_gamma g gpre" by (cases) simp
  then have "la \<in> set (firstGamma (gpre @ NT x # gsuf) nu fi)"
    using Cons.IH Cons.prems(1,3,4) by blast
  then show ?case using \<open>nullableSym s nu\<close> by auto
qed

lemma firstPass_preserves_key_value_subset: "fmlookup fi x = Some xFirst
  \<Longrightarrow> \<exists>xFirst'. fmlookup (firstPass ps nu fi) x = Some xFirst' \<and> set xFirst \<subseteq> set xFirst'"
proof (induction ps arbitrary: x)
  case Nil
  then show ?case unfolding firstPass_def by auto
next
  case (Cons p ps)
  then obtain y gamma where "p = (y, gamma)" by fastforce
  let ?fi' = "firstPass ps nu fi"
  let ?fg = "firstGamma gamma nu ?fi'"
  let ?yFirst = "findOrEmpty y ?fi'"
  let ?yFirst' = "?yFirst @@ ?fg"
  obtain xFirst' where "fmlookup ?fi' x = Some xFirst'" and "set xFirst \<subseteq> set xFirst'"
    using Cons by auto
  show ?case
  proof (cases "?yFirst = ?yFirst'")
    case True
    then have "fmlookup (firstPass (p # ps) nu fi) x = fmlookup ?fi' x" by
      (simp add: \<open>p = (y, gamma)\<close> unfold_updateFi)
    then show ?thesis using \<open>fmlookup ?fi' x = Some xFirst'\<close> \<open>set xFirst \<subseteq> set xFirst'\<close> by simp
  next
    case False
    show ?thesis
    proof (cases "x = y")
      case True
      then have "fmlookup (firstPass (p # ps) nu fi) x = Some ?yFirst'" using False by
        (auto simp add: \<open>p = (y, gamma)\<close> unfold_updateFi list_union_def)
      moreover have "set xFirst' \<subseteq> set ?yFirst'"
        using True \<open>fmlookup ?fi' x = Some xFirst'\<close> findOrEmpty_def in_findOrEmpty_exists_set
        by fastforce
      ultimately show ?thesis using \<open>set xFirst \<subseteq> set xFirst'\<close> by blast
    next
      case False
      then have "fmlookup (firstPass (p # ps) nu fi) x = fmlookup ?fi' x"
        by (simp add: \<open>p = (y, gamma)\<close> unfold_updateFi)
      then show ?thesis using \<open>fmlookup ?fi' x = Some xFirst'\<close> \<open>set xFirst \<subseteq> set xFirst'\<close> by simp
    qed
  qed
qed

lemma firstPass_equiv_cons_tl: assumes "fi = firstPass (p # ps) nu fi"
  shows "fi = firstPass ps nu fi"
proof-
  obtain x gamma where "p = (x, gamma)" by fastforce
  let ?fi' = "firstPass ps nu fi"
  let ?fg = "firstGamma gamma nu ?fi'"
  let ?xFirst = "findOrEmpty x ?fi'"
  let ?xFirst' = "?xFirst @@ ?fg"
  show "fi = firstPass ps nu fi"
  proof (cases "?xFirst = ?xFirst'")
    case True
    then show ?thesis using True assms by (auto simp add: \<open>p = (x, gamma)\<close> unfold_updateFi)
  next
    case False
    show ?thesis
    proof -
      have "fi = fmupd x ?xFirst' ?fi'" using False assms by
        (simp add: \<open>p = (x, gamma)\<close> unfold_updateFi list_union_def split: if_splits)
      then have "fmlookup fi x = Some ?xFirst'" by (metis fmupd_lookup)
      have "firstPass ps nu fi = fi"
        by (metis assms firstPass_cons_subset firstPass_subset pairsOf_inj subset_antisym)
      then have "firstGamma gamma nu (firstPass ps nu fi) = []"
        using \<open>fmlookup fi x = Some ?xFirst'\<close> False
        unfolding findOrEmpty_def by (auto split: option.splits)
      moreover have "firstGamma gamma nu (firstPass ps nu fi) \<noteq> []"
        by (metis False append_self_conv empty_iff filter_True list.set(1) list_union_def)
      ultimately show "fi = firstPass ps nu fi" by auto
    qed
  qed
qed

lemma firstPass_equiv_right_t': "(lx, gpre @ (T y) # gsuf) \<in> set psuf \<Longrightarrow> nullable_set_for nu g
  \<Longrightarrow> nullable_gamma g gpre \<Longrightarrow> fi = firstPass psuf nu fi \<Longrightarrow> prods g = ppre @ psuf
  \<Longrightarrow> (\<exists>lxFirst. fmlookup fi lx = Some lxFirst \<and> (LA y) \<in> set lxFirst)"
proof (induction psuf arbitrary: ppre)
  case Nil
  then show ?case by auto
next
  case (Cons p psuf)
  obtain lx' gamma where "p = (lx', gamma)" by fastforce
  from Cons.prems(1) consider (prod_is_p) "(lx, gpre @ T y # gsuf) = p"
    | (prod_in_psuf) "(lx, gpre @ T y # gsuf) \<in> set psuf" by auto
  then show ?case
  proof (cases)
    case prod_is_p
    let ?fi' = "firstPass psuf nu fi"
    let ?fg = "firstGamma (gpre @ T y # gsuf) nu ?fi'"
    let ?lxFirst = "findOrEmpty lx ?fi'"
    let ?lxFirst' = "?lxFirst @@ ?fg"
    from Cons.prems(4) have " fi = firstPass ((lx, gpre @ T y # gsuf) # psuf) nu fi"
      using prod_is_p by blast
    then consider (same) "?lxFirst = ?lxFirst'" "fi = firstPass psuf nu fi"
      | (new) "?lxFirst \<noteq> ?lxFirst'" "fi = fmupd lx ?lxFirst' ?fi'"
      by (metis Nil_is_append_conv firstPass_cons list_union_def unfold_updateFi)
    then show ?thesis
    proof (cases)
      case same
      have "LA y \<in> set ?fg" using Cons.prems(2,3) by - (rule la_in_firstGamma_t, auto)
      then have "LA y \<in> set ?lxFirst" using same(1) by (auto intro: mem_list_union)
      then have "LA y \<in> set (findOrEmpty lx fi)" using same(2) by auto
      then show ?thesis by (simp add: in_findOrEmpty_exists_set)
    next
      case new
      from new(2) obtain lxFirst where "fmlookup fi lx = Some lxFirst" and "?lxFirst' = lxFirst" by
        (metis fmupd_lookup)
      then have "LA y \<in> set lxFirst" using la_in_firstGamma_t Cons.prems(2,3) by fastforce
      then show ?thesis using \<open>fmlookup fi lx = Some lxFirst\<close> by simp
    qed
  next
    case prod_in_psuf
    then have "(lx, gpre @ T y # gsuf) \<in> set psuf" by auto
    moreover have "fi = firstPass psuf nu fi" using Cons.prems(4) firstPass_equiv_cons_tl by blast
    moreover have "prods g = (ppre @ [p]) @ psuf" by (simp add: Cons.prems(5))
    ultimately show ?thesis using Cons.prems(2,3) by
      - (rule Cons.IH[where ppre = "ppre @ [p]"], auto)
  qed
qed

lemma firstPass_equiv_right_t: "(lx, gpre @ (T y) # gsuf) \<in> set (prods g) \<Longrightarrow> nullable_set_for nu g
  \<Longrightarrow> nullable_gamma g gpre \<Longrightarrow> fi = firstPass (prods g) nu fi
  \<Longrightarrow> \<exists>lxFirst. fmlookup fi lx = Some lxFirst \<and> LA y \<in> set lxFirst"
  by (simp add: firstPass_equiv_right_t')

lemma firstPass_equiv_right_nt': "nullable_set_for nu g \<Longrightarrow> fi = firstPass psuf nu fi
  \<Longrightarrow> (lx, gpre @ (NT rx) # gsuf) \<in> set psuf \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> fmlookup fi rx = Some rxFirst \<Longrightarrow> la \<in> set rxFirst \<Longrightarrow> ppre @ psuf = (prods g)
  \<Longrightarrow> \<exists>lxFirst. fmlookup fi lx = Some lxFirst \<and> la \<in> set lxFirst"
proof (induction psuf arbitrary: ppre)
  case Nil
  then show ?case by auto
next
  case (Cons p psuf)
  obtain lx' gamma where "p = (lx', gamma)" by fastforce
  from Cons.prems(1) consider (prod_is_p) "(lx, gpre @ NT rx # gsuf) = p"
    | (prod_in_psuf) "(lx, gpre @ NT rx # gsuf) \<in> set psuf" using Cons.prems(3) by auto
  then show ?case
  proof (cases)
    case prod_is_p
    let ?fi' = "firstPass psuf nu fi"
    let ?fg = "firstGamma (gpre @ NT rx # gsuf) nu ?fi'"
    let ?lxFirst = "findOrEmpty lx ?fi'"
    let ?lxFirst' = "?lxFirst @@ ?fg"
    from Cons.prems(2) have "fi = firstPass ((lx, gpre @ NT rx # gsuf) # psuf) nu fi"
      using prod_is_p by blast
    then consider (same) "?lxFirst = ?lxFirst'" "fi = firstPass psuf nu fi"
      | (new) "?lxFirst \<noteq> ?lxFirst'" "fi = fmupd lx ?lxFirst' ?fi'"
      using firstPass_cons la_in_firstGamma_nt[OF Cons.prems(1,4-6)]
        unfold_updateFi[where gamma = "gpre @ NT rx # gsuf"]
      unfolding list_union_def
      by (auto split: if_splits)
    then show ?thesis
    proof (cases)
      case same
      then have "la \<in> set (findOrEmpty lx fi)" using Cons.prems(1,4,5,6) la_in_firstGamma_nt by
          (metis mem_list_union)
      then show ?thesis by (simp add: in_findOrEmpty_exists_set)
    next
      case new
      have "la \<in> set ?lxFirst'"
      proof (rule list_union_I2)
        from Cons.prems(2) have "fi = firstPass psuf nu fi" by (rule firstPass_equiv_cons_tl)
        then have "fmlookup (firstPass psuf nu fi) rx = Some rxFirst" using Cons.prems(5) by auto
        then show "la \<in> set ?fg"
          using Cons.prems(1,4,6) \<open>fi = firstPass ((lx, gpre @ NT rx # gsuf) # psuf) nu fi\<close>
          by - (rule la_in_firstGamma_nt[where xFirst = "rxFirst"])
      qed
      then show ?thesis by (metis fmupd_lookup new(2))
    qed
  next
    case prod_in_psuf
    then have "(lx, gpre @ NT rx # gsuf) \<in> set psuf" by auto
    moreover have "fi = firstPass psuf nu fi" using Cons.prems(2) firstPass_equiv_cons_tl by blast
    moreover have "prods g = (ppre @ [p]) @ psuf" by (simp add: Cons.prems(7))
    ultimately show ?thesis using Cons.prems(1,4,5,6,7) prod_in_psuf by
      - (rule Cons.IH[where ppre = "ppre @ [p]"], auto)
  qed
qed

lemma firstPass_equiv_right_nt: "nullable_set_for nu g \<Longrightarrow> fi = firstPass (prods g) nu fi
  \<Longrightarrow> (lx, gpre @ (NT rx) # gsuf) \<in> set (prods g) \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> fmlookup fi rx = Some rxFirst \<Longrightarrow> la \<in> set rxFirst
  \<Longrightarrow> \<exists>lxFirst. fmlookup fi lx = Some lxFirst \<and> la \<in> set lxFirst"
  by (simp add: firstPass_equiv_right_nt')

lemma firstPass_equiv_complete: assumes "nullable_set_for nu g" "fi = firstPass (prods g) nu fi"
  shows "first_map_complete fi g"
proof -
  have "first_sym g la s
    \<Longrightarrow> (\<forall>x. s = NT x \<longrightarrow> (\<exists> xFirst. fmlookup fi x = Some xFirst \<and> la \<in> set xFirst))" for la s
  proof (induction rule: first_sym.induct)
    case (FirstT)
    then show ?case by blast
  next
    case (FirstNT lx gpre s gsuf la)
    then show ?case
    proof (cases s)
      case (NT rx)
      then obtain rxFirst where "fmlookup fi rx = Some rxFirst \<and> la \<in> set rxFirst"
        using FirstNT.IH by auto
      then show ?thesis using FirstNT.hyps(1,2) NT assms firstPass_equiv_right_nt by fastforce
    next
      case (T y)
      from FirstNT.hyps(3) have "la = LA y" by (cases) (auto simp add: T)
      then show ?thesis using firstPass_equiv_right_t using FirstNT.hyps(1,2) T assms by fastforce
    qed
  qed
  then show ?thesis by (simp add: first_map_complete_def)
qed

lemma mkFirstMap'_complete: "nullable_set_for nu g \<Longrightarrow> all_pairs_are_first_candidates fi (prods g)
  \<Longrightarrow> first_map_complete (the (mkFirstMap' (prods g) nu fi)) g"
proof (induction "countFirstCands (prods g) fi" arbitrary: fi rule: less_induct)
  case less
  let ?fi' = "firstPass (prods g) nu fi"
  obtain fi' where fi'_def: "mkFirstMap' (prods g) nu ?fi' = Some fi'"
    by (meson firstPass_preserves_apac less.prems(2) mkFirstMap'_dom_if_apac not_Some_eq)
  moreover have "first_map_complete (if fi = ?fi' then fi else fi') g"
  proof (cases "fi = ?fi'")
    case True
    then show ?thesis using firstPass_equiv_complete less.prems(1) by auto
  next
    case False
    have "countFirstCands (prods g) ?fi' < countFirstCands (prods g) fi" by
      (simp add: False firstPass_not_equiv_candidates_lt firstPass_preserves_apac less.prems(2))
    moreover have "nullable_set_for nu g" by (simp add: less.prems(1))
    moreover have "all_pairs_are_first_candidates ?fi' (prods g)" by
      (simp add: firstPass_preserves_apac less.prems(2))
    ultimately show ?thesis
      using fi'_def less.hyps by force
  qed
  ultimately show ?case by (auto simp add: mkFirstMap'.simps Let_def)
qed

theorem mkFirstMap_complete: "nullable_set_for nu g \<Longrightarrow> first_map_complete (mkFirstMap g nu) g"
  unfolding mkFirstMap_def
  using empty_fi_apac mkFirstMap'_complete by fastforce

theorem mkFirstMap_correct: "nullable_set_for nu g \<Longrightarrow> first_map_for (mkFirstMap g nu) g"
  using mkFirstMap_sound mkFirstMap_complete
  by fastforce

declare mkFirstMap'.simps[code]

end