section \<open> ApproxMC certification for CNF-XOR \<close>

text \<open>
  This concretely instantiates the locales with a syntax and
  semantics for CNF-XOR, giving us a certificate checker for
  approximate counting in this theory.
\<close>

theory CertCheck_CNF_XOR imports
  ApproxMCAnalysis
  CertCheck
  HOL.String "HOL-Library.Code_Target_Numeral"
  Show.Show_Real
begin

text \<open>
  This follows CryptoMiniSAT's CNF-XOR formula syntax.
  A clause is a list of literals (one of which must be satisfied).
  An XOR constraint has the form $l_1 + l_2 + \dots + l_n = 1$ where addition is taken over $F_2$.
  Syntactically, they are specified by the list of LHS literals.
  Variables are natural numbers (in practice, variable 0 is never used)
\<close>

datatype lit = Pos nat | Neg nat
type_synonym clause = "lit list"
type_synonym cmsxor = "lit list"
type_synonym fml = "clause list \<times> cmsxor list"

type_synonym assignment = "nat \<Rightarrow> bool"

definition sat_lit :: "assignment \<Rightarrow> lit \<Rightarrow> bool" where
  "sat_lit w l = (case l of Pos x \<Rightarrow> w x | Neg x \<Rightarrow> \<not>w x)"

definition sat_clause :: "assignment \<Rightarrow> clause \<Rightarrow> bool" where
  "sat_clause w C = (\<exists>l \<in> set C. sat_lit w l)"

definition sat_cmsxor :: "assignment \<Rightarrow> cmsxor \<Rightarrow> bool" where
  "sat_cmsxor w C = odd ((sum_list (map (of_bool \<circ> (sat_lit w)) C))::nat)"

definition sat_fml :: "assignment \<Rightarrow> fml \<Rightarrow> bool"
  where
  "sat_fml w f = (
    (\<forall>C \<in> set (fst f). sat_clause w C) \<and>
    (\<forall>C \<in> set (snd f). sat_cmsxor w C))"

(* The solution set *)
definition sols :: "fml \<Rightarrow> assignment set"
  where "sols f = {w. sat_fml w f}"

lemma sat_fml_cons[simp]:
  shows
  "sat_fml w (FC, x # FX) \<longleftrightarrow>
  sat_fml w (FC,FX) \<and> sat_cmsxor w x"
  "sat_fml w (c # FC, FX) \<longleftrightarrow>
  sat_fml w (FC,FX) \<and> sat_clause w c"
  unfolding sat_fml_def by auto

(* Construct clauses for a given XOR *)
fun enc_xor :: "nat xor \<Rightarrow> fml \<Rightarrow> fml"
  where
    "enc_xor (x,b) (FC,FX) = (
    if b then (FC, map Pos x # FX)
    else
      case x of
        [] \<Rightarrow> (FC,FX)
      | (v#vs) \<Rightarrow> (FC, (Neg v # map Pos vs) # FX))"

lemma sols_enc_xor:
  shows "sols (enc_xor (x,b) (FC,FX)) =
       sols (FC,FX) \<inter> {\<omega>. satisfies_xorL (x,b) \<omega>}"
  unfolding sols_def
  by (cases x; auto simp add: satisfies_xorL_def sat_cmsxor_def o_def sat_lit_def list.case_eq_if)

(* Solution checking *)
definition check_sol :: "fml \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  where "check_sol fml w = (
  list_all (list_ex (sat_lit w)) (fst fml) \<and>
  list_all (sat_cmsxor w) (snd fml))"

definition ban_sol :: "(nat \<times> bool) list \<Rightarrow> fml \<Rightarrow> fml"
  where "ban_sol vs fml =
    ((map (\<lambda>(v,b). if b then Neg v else Pos v) vs)#fst fml, snd fml)"

lemma check_sol_sol:
  shows "w \<in> sols F \<longleftrightarrow>
  check_sol F w"
  unfolding check_sol_def sols_def sat_fml_def
  apply clarsimp
  by (metis Ball_set_list_all Bex_set_list_ex sat_clause_def)

lemma ban_sat_clause:
  shows "sat_clause w (map (\<lambda>(v, b). if b then Neg v else Pos v) vs) \<longleftrightarrow>
    map w (map fst vs) \<noteq> map snd vs"
  unfolding sat_clause_def
  by (force simp add: sat_lit_def split: if_splits)

lemma sols_ban_sol:
  shows"sols (ban_sol vs F) =
       sols F \<inter>
       {\<omega>. map \<omega> (map fst vs) \<noteq> map snd vs}"
  unfolding ban_sol_def sols_def
  by (auto simp add: ban_sat_clause)

(* Globally interpret the ApproxMC locale to make
    ApproxMC certification available for CNF-XOR *)
global_interpretation CertCheck_CNF_XOR :
  CertCheck "sols" "enc_xor" "check_sol" "ban_sol"
  defines
    random_seed_xors = CertCheck_CNF_XOR.random_seed_xors and
    fix_t = CertCheck_CNF_XOR.appmc.fix_t and
    find_t = CertCheck_CNF_XOR.find_t and
    BSAT = CertCheck_CNF_XOR.BSAT and
    check_BSAT_sols = CertCheck_CNF_XOR.check_BSAT_sols and
    size_xorL_cert = CertCheck_CNF_XOR.size_xorL_cert and
    approxcore_xorsL = CertCheck_CNF_XOR.approxcore_xorsL and
    fold_approxcore_xorsL_cert = CertCheck_CNF_XOR.fold_approxcore_xorsL_cert and
    approxcore_xorsL_cert = CertCheck_CNF_XOR.approxcore_xorsL_cert and
    calc_median = CertCheck_CNF_XOR.calc_median and
    certcheck = CertCheck_CNF_XOR.certcheck
  apply unfold_locales
  subgoal by (metis sols_enc_xor surj_pair)
  subgoal by (metis sols_ban_sol)
  by (metis check_sol_sol)

(* Note that we automatically get the associated theorems
thm CertCheck_CNF_XOR.certcheck_sound

thm CertCheck_CNF_XOR.certcheck_promise_complete
*)

subsection \<open> Blasting XOR constraints to CNF \<close>

text \<open>
  This formalizes the usual linear conversion from CNF-XOR into CNF.
  It is not necessary to use this conversion for solvers that support
  CNF-XOR formulas natively.
\<close>

definition negate_lit :: "lit \<Rightarrow> lit"
  where "negate_lit l = (case l of Pos x \<Rightarrow> Neg x | Neg x \<Rightarrow> Pos x)"

(* Naive direct encoding XOR *)
fun xor_clauses :: "cmsxor \<Rightarrow> bool \<Rightarrow> clause list"
  where
    "xor_clauses [] b = (if b then [[]] else [])"
  | "xor_clauses (x#xs) b =
    (let p_x = xor_clauses xs b in
     let n_x = xor_clauses xs (\<not>b) in
       map (\<lambda>c. x # c) p_x @ map (\<lambda>c. negate_lit x # c) n_x)"

lemma sat_cmsxor_nil[simp]:
  shows"\<not> (sat_cmsxor w [])"
  unfolding sat_cmsxor_def
  by auto

lemma sat_cmsxor_cons:
  shows "sat_cmsxor w (x # xs) =
    (if sat_lit w x then \<not> (sat_cmsxor w xs) else sat_cmsxor w xs)"
  unfolding sat_cmsxor_def
  by auto

lemma sat_cmsxor_append:
  shows "sat_cmsxor w (xs @ ys) =
    (if sat_cmsxor w xs then \<not> (sat_cmsxor w ys) else sat_cmsxor w ys)"
proof (induction xs)
  case Nil
  then show ?case
    by (auto simp add: sat_cmsxor_def)
next
  case (Cons x xs)
  then show ?case
    by (auto simp add: sat_cmsxor_cons)
qed

definition sat_clauses:: "assignment \<Rightarrow> clause list \<Rightarrow> bool"
  where "sat_clauses w cs = (\<forall>c \<in> set cs. sat_clause w c)"

lemma sat_clauses_append:
  shows "sat_clauses w (xs @ ys) =
    (sat_clauses w xs \<and> sat_clauses w ys)"
  unfolding sat_clauses_def by auto

lemma sat_clauses_map:
  shows "sat_clauses w (map ((#) x) cs) =
    (sat_lit w x \<or> sat_clauses w cs)"
  unfolding sat_clauses_def sat_clause_def by auto

lemma sat_lit_negate_lit[simp]:
  "sat_lit w (negate_lit l) = (\<not>sat_lit w l)"
  apply (cases l)
  by (auto simp add: negate_lit_def sat_lit_def)

lemma sols_xor_clauses:
  shows "
    sat_clauses w (xor_clauses xs b) \<longleftrightarrow>
    (sat_cmsxor w xs = b)"
proof (induction xs arbitrary: b)
  case Nil
  then show ?case
    by (auto simp add: sat_cmsxor_def sat_clauses_def sat_clause_def)
next
  case (Cons x xs b)
  have *: "(sat_cmsxor w (x # xs) = b) =
    (if sat_lit w x
     then (sat_cmsxor w xs = (\<not>b))
     else (sat_cmsxor w xs = b))" unfolding sat_cmsxor_cons
    by auto

  have "sat_clauses w (xor_clauses (x # xs) b) \<longleftrightarrow>
    ((sat_lit w x \<or> sat_clauses w (xor_clauses xs b)) \<and>
     (\<not>(sat_lit w x) \<or> sat_clauses w (xor_clauses xs (\<not> b))))"
    unfolding xor_clauses.simps Let_def sat_clauses_append sat_clauses_map
    by auto
  moreover have "... = (
     (sat_lit w x \<or> (sat_cmsxor w xs = b)) \<and>
     (\<not>(sat_lit w x) \<or> (sat_cmsxor w xs = (\<not> b))))"
    using Cons.IH by auto
  moreover have "... = (sat_cmsxor w (x # xs) = b)"
    unfolding * by auto
  ultimately show ?case
    by auto
qed

(* This can be done more generally with freshness *)
definition var_lit :: "lit \<Rightarrow> nat"
  where "var_lit l = (case l of Pos x \<Rightarrow> x  | Neg x \<Rightarrow> x)"

definition var_lits :: "lit list \<Rightarrow> nat"
  where "var_lits ls = fold max (map var_lit ls) 0"

lemma sat_lit_same:
  assumes "\<And>x. x \<le> var_lit l \<Longrightarrow> w x = w' x"
  shows "sat_lit w l = sat_lit w' l"
  using assms
  apply (cases l)
  by (auto simp add: sat_lit_def var_lit_def)

lemma var_lits_eq:
  "var_lits ls = Max (set (0 # map var_lit ls))"
  unfolding var_lits_def Max.set_eq_fold
  by auto

lemma sat_lits_same:
  assumes "\<And>x. x \<le> var_lits c \<Longrightarrow> w x = w' x"
  shows "sat_clause w c = sat_clause w' c"
  using assms
  unfolding sat_clause_def var_lits_eq sat_lit_same
  by (smt (verit) List.finite_set Max_ge dual_order.trans image_subset_iff list.set_map sat_lit_same set_subset_Cons)

lemma le_var_lits_in:
  assumes "y \<in> set ys" "v \<le> var_lit y"
  shows "v \<le> var_lits ys"
  using assms unfolding var_lits_eq
  by (metis List.finite_set Max_ge dual_order.trans imageI insertCI list.set(2) list.set_map)

lemma sat_cmsxor_same:
  assumes "\<And>x. x \<le> var_lits xs \<Longrightarrow> w x = w' x"
  shows "sat_cmsxor w xs = sat_cmsxor w' xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    unfolding sat_cmsxor_def
    by auto
next
  case ih:(Cons x xs)
  have 1: "sat_lit w x = sat_lit w' x"
    apply (intro sat_lit_same)
    using ih(2)
    by (metis le_var_lits_in list.set_intros(1))
  have 2: "sat_cmsxor w xs = sat_cmsxor w' xs"
    apply (intro ih(1))
    using ih(2)
    by (smt (verit) List.finite_set Max_ge_iff empty_not_insert insert_iff list.set(2) list.simps(9) var_lits_eq)
  show ?case
    unfolding sat_cmsxor_cons
    using 1 2 by presburger
qed

(* linear *)
lemma sat_cmsxor_split:
  assumes u: "var_lits xs < u" "var_lits ys < u"
  assumes w': "w' = (\<lambda>x. if x = u then \<not> sat_cmsxor w xs else w x)"
  shows "
   (sat_cmsxor w (xs @ ys) =
    (sat_cmsxor w' (Pos u # xs) \<and>
    sat_cmsxor w' (Neg u # ys)))"
proof -
  have xs: "sat_cmsxor w' xs = sat_cmsxor w xs"
    apply (intro sat_cmsxor_same)
    using u unfolding w' by auto
  have ys: "sat_cmsxor w' ys = sat_cmsxor w ys"
    apply (intro sat_cmsxor_same)
    using u unfolding w' by auto

  show ?thesis
    unfolding sat_cmsxor_append sat_cmsxor_cons xs ys
    unfolding w' by (auto simp add: sat_lit_def)
qed

(* split an XOR constraint into chunks of at most k+3 literals *)
fun split_xor ::"nat \<Rightarrow> cmsxor \<Rightarrow> cmsxor list \<times> nat \<Rightarrow> cmsxor list \<times> nat"
  where "split_xor k xs (acc,u) = (
    if length xs \<le> k + 3 then (xs # acc, u)
    else (
      let xs1 = take (k + 2) xs in
      let xs2 = drop (k + 2) xs in
      split_xor k (Neg u # xs2) ((Pos u # xs1) # acc, u+1)
    )
  )"

declare split_xor.simps[simp del]

lemma split_xor_bound:
  assumes "split_xor k xs (acc,u) = (acc',u')"
  shows  "u \<le> u'"
  using assms
proof (induction "length xs" arbitrary: xs acc u acc' u' rule: less_induct)
  case less
  have " length xs \<le> k + 3 \<or> \<not> ( length xs \<le> k + 3)" by auto
  moreover {
    assume "length xs \<le> k + 3"
    then have "u \<le> u'"
      using less(2) split_xor.simps by auto
  }
  moreover {
    assume s: "\<not> ( length xs \<le> k + 3)"
    then have l: "length (Neg u # drop (Suc (Suc k)) xs) < length xs"
      by auto
    have "Suc u \<le> u'"
      using s less(2)
      unfolding split_xor.simps[of k xs]
      using less(1)[OF l] by auto
    then have "u \<le> u'" by auto
  }
  ultimately show ?case by auto
qed

lemma var_lits_append:
  shows "var_lits xs \<le> var_lits (xs @ ys)"
    "var_lits ys \<le> var_lits (xs @ ys)"
  unfolding var_lits_eq
  by auto

lemma fold_max_eq:
  assumes "i \<le> u"
  shows "fold max ls u = max u (fold max ls (i::nat))"
  using assms
  apply (induction ls arbitrary: i)
  subgoal by clarsimp
  apply clarsimp
  by (smt (verit) List.finite_set Max.set_eq_fold Max_ge_iff empty_iff insert_iff list.set(2) max.orderI max_def pre_arith_simps(3))

(* We can be more precise here that the number of solutions
  is preserved exactly, but for UNSAT this is not needed *)
lemma split_xor_sound:
  assumes "sat_cmsxor w xs" "\<And>x. x \<in> set acc \<Longrightarrow> sat_cmsxor w x"
  assumes u: "var_lits xs < u" "\<And>x. x \<in> set acc \<Longrightarrow> var_lits x < u"
  assumes "split_xor k xs (acc,u) = (acc',u')"
  obtains w' where
    "\<And>x. x < u \<Longrightarrow> w x = w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> sat_cmsxor w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> var_lits x < u'"
  using assms
proof (induction "length xs" arbitrary: w xs acc u acc' u' thesis rule: less_induct)
  case less
  have " length xs \<le> k + 3 \<or> \<not> ( length xs \<le> k + 3)" by auto
  moreover {
    assume "length xs \<le> k + 3"
    then have *: "acc' = xs # acc"
      using less(7) split_xor.simps
      by auto
    then have
    "\<And>x. x < u \<Longrightarrow> w x = w x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> sat_cmsxor w x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> var_lits x < u'"
      subgoal by meson
      subgoal using less
        by (metis * set_ConsD)
      using less
      by (metis "*" order_trans_rules(22) set_ConsD split_xor_bound)
  }
  moreover {
    assume s: "\<not> (length xs \<le> k + 3)"
    define xs1 where xs1:"xs1 = take (k + 2) xs"
    define xs2 where xs2:"xs2 = drop (k + 2) xs"
    have sp: "split_xor k (Neg u # xs2) ((Pos u # xs1) # acc, u+1) = (acc',u')"
      by (metis less(7) s split_xor.simps xs1 xs2)
    have l: "length (Neg u # xs2) < length xs"
      using s xs2 by auto

    have xs: "xs = xs1 @ xs2" by (simp add: xs1 xs2)

    define w' where w': "w' =
    (\<lambda>x. if x = u then \<not> sat_cmsxor w xs1 else w x)"

    have vl: "var_lits xs1 < u" "var_lits xs2 < u"
      apply (metis less(5) order_trans_rules(21) var_lits_append(1) xs)
      by (metis less(5) order_trans_rules(21) var_lits_append(2) xs)

    from sat_cmsxor_split[OF this w']
    have satws1: "sat_cmsxor w' (Pos u # xs1)"
     and satws2: "sat_cmsxor w' (Neg u # xs2)"
      using less(3) xs by auto

    have satacc: "\<And>x. x \<in> set ((Pos u # xs1) # acc) \<Longrightarrow>
        sat_cmsxor w' x"
      by (metis less(4) less(6) not_less sat_cmsxor_same satws1 set_ConsD w')

    have v1: "var_lits (Neg u # xs2) < u + 1"
      unfolding var_lits_def
      apply (simp add: var_lit_def)
      using vl var_lits_def fold_max_eq
      by (metis le_add2 le_add_same_cancel2 less_Suc_eq max.absorb3)

    have "fold max (map var_lit xs1) u < Suc u"
      using vl var_lits_def
      by (smt (verit, best) List.finite_set Max.set_eq_fold Max_ge_iff dual_order.trans empty_iff insert_iff lessI less_or_eq_imp_le list.set(2) not_less)
    moreover have "\<And>x. x \<in> set acc \<Longrightarrow>
         fold max (map var_lit x) 0 < Suc u"
      by (metis less(6) less_SucI var_lits_def)
    ultimately have v2:"\<And>x. x \<in> set ((Pos u # xs1) # acc) \<Longrightarrow> var_lits x < u + 1"
      unfolding var_lits_def
      by (auto simp add: var_lit_def)

    obtain w'' where
    w'': "\<And>x. x < u + 1 \<Longrightarrow> w' x = w'' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> sat_cmsxor w'' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> var_lits x < u'"
      using less(1)[OF l _ satws2 satacc v1 v2 sp]
      by auto

    have "\<And>x. x < u \<Longrightarrow> w x = w'' x"
      using w''(1)
      unfolding w'
      using less_Suc_eq by fastforce

    then have "\<exists>w''. (
         (\<forall>x. x < u \<longrightarrow> w x = w'' x) \<and>
          (\<forall>x. x \<in> set acc' \<longrightarrow> sat_cmsxor w'' x) \<and>
          (\<forall>x. x \<in> set acc' \<longrightarrow> var_lits x < u'))"
      using w''(2-3) by auto
  }
  ultimately show ?case
    using less(2)
    by (metis (mono_tags, lifting))
qed

definition split_xors ::"nat \<Rightarrow> nat \<Rightarrow> cmsxor list \<Rightarrow> cmsxor list"
where "split_xors k u xs = fst (fold (split_xor k) xs ([],u))"

lemma split_xors_sound:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> sat_cmsxor w x"
          "\<And>x. x \<in> set acc \<Longrightarrow> sat_cmsxor w x"
  assumes u: "\<And>x. x \<in> set xs \<Longrightarrow> var_lits x < u"
      "\<And>x. x \<in> set acc \<Longrightarrow> var_lits x < u"
  assumes "fold (split_xor k) xs (acc,u) = (acc',u')"
  obtains w' where
    "\<And>x. x < u \<Longrightarrow> w x = w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> sat_cmsxor w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> var_lits x < u'"
  using assms
proof (induction xs arbitrary: w acc u acc' u')
  case Nil
  then show ?case
    by auto
next
  case ih:(Cons x xs)
  obtain acc'' u'' where x: "split_xor k x (acc, u) = (acc'',u'')"
    by fastforce
  from split_xor_sound[OF _ _ _ _ this]
  obtain w'' where
    w'': "\<And>x. x < u \<Longrightarrow> w x = w'' x"
    "\<And>x. x \<in> set acc'' \<Longrightarrow> sat_cmsxor w'' x"
    "\<And>x. x \<in> set acc'' \<Longrightarrow> var_lits x < u''"
    by (smt (verit, del_insts) ih(4) ih(5) ih(6) ih.prems(2) list.set_intros(1))
  have rw: "fold (split_xor k) xs (acc'',u'') = (acc', u')"
    using ih(7) x by auto
  have 1: "\<And>x. x \<in> set xs \<Longrightarrow>sat_cmsxor w'' x"
    by (metis basic_trans_rules(22) ih(3) ih(5) list.set_intros(2) not_less sat_cmsxor_same w''(1))
  have 2: "\<And>x. x \<in> set xs \<Longrightarrow> var_lits x < u''"
    by (meson ih(5) list.set_intros(2) order_trans_rules(22) split_xor_bound x)
  show ?case
    using ih(1)[OF _ 1 w''(2) 2 w''(3) rw]
    by (smt (verit, best) basic_trans_rules(22) ih(2) split_xor_bound w''(1) x)
qed

(* maximum variable occuring in the whole formula *)
definition var_fml :: "fml \<Rightarrow> nat"
  where "var_fml f =
  max (fold max (map var_lits (fst f)) 0)
      (fold max (map var_lits (snd f)) 0)"

lemma var_fml_eq:
  "var_fml f =
    max (Max (set (0 # map var_lits (fst f))))
    (Max (set (0 # map var_lits (snd f))))"
  unfolding var_fml_def Max.set_eq_fold
  by auto

definition split_fml ::" nat \<Rightarrow> fml \<Rightarrow> fml"
  where "split_fml k f = (
  let u = var_fml f + 1 in
    (fst f, (split_xors k u (snd f)))
  )"

lemma var_lits_var_fml:
  shows "\<And>x. x \<in> set (snd F) \<Longrightarrow> var_lits x \<le> var_fml F"
  "\<And>x. x \<in> set (fst F) \<Longrightarrow> var_lits x \<le> var_fml F"
  unfolding var_fml_eq
  subgoal
    apply clarsimp
    by (meson List.finite_set Max_ge finite_imageI finite_insert image_subset_iff max.coboundedI2 subset_insertI)
  apply clarsimp
  by (meson List.finite_set Max_ge finite_imageI finite_insert image_subset_iff max.coboundedI1 subset_insertI)

lemma split_fml_satisfies:
  assumes "sat_fml w F"
  obtains w' where "sat_fml w' (split_fml k F)"
proof -
  obtain acc' u' where
    *: "fold (split_xor k) (snd F) ([], var_fml F + 1) = (acc',u')"
    by fastforce
  have 1:"\<And>x. x \<in> set (snd F) \<Longrightarrow> sat_cmsxor w x"
    using assms unfolding sat_fml_def by auto
  have 2:"\<And>x. x \<in> set (snd F) \<Longrightarrow> var_lits x < var_fml F + 1"
    using var_lits_var_fml
    by (meson less_add_one order_le_less_trans)
  from split_xors_sound[OF 1 _ _ 2 *]
  obtain w' where
    w': "\<And>x. x < var_fml F + 1 \<Longrightarrow> w x = w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> sat_cmsxor w' x"
    "\<And>x. x \<in> set acc' \<Longrightarrow> var_lits x < u'"
    using "2" by auto
  have "\<And>x. x \<in> set (fst F) \<Longrightarrow> sat_clause w' x"
    by (metis assms less_add_one order_trans_rules(21) sat_fml_def sat_lits_same var_lits_var_fml(2) w'(1))

  then have "sat_fml w' (split_fml k F)"
    unfolding split_fml_def Let_def split_xors_def *
    by (auto simp add: sat_fml_def w'(2))
  thus ?thesis
    using that by auto
qed

lemma split_fml_sols:
  assumes "sols (split_fml k F) = {}"
  shows "sols F = {}"
  using assms
  using split_fml_satisfies unfolding sols_def
  by (metis Collect_empty_eq)

definition blast_xors :: "cmsxor list \<Rightarrow> clause list"
  where "blast_xors xors =  concat (map (\<lambda>x. xor_clauses x True) xors)"

definition blast_fml :: "fml \<Rightarrow> clause list"
  where "blast_fml f =
    fst f @ blast_xors (snd f)"

lemma sat_clauses_concat:
  "sat_clauses w (concat xs) \<longleftrightarrow>
  (\<forall>x \<in> set xs. sat_clauses w x)"
  unfolding sat_clauses_def
  by auto

lemma blast_xors_sound:
  assumes "(\<And>x. x \<in> set xors \<Longrightarrow> sat_cmsxor w x)"
  shows "sat_clauses w (blast_xors xors)"
  unfolding blast_xors_def sat_clauses_concat
  by (auto simp add: assms sols_xor_clauses)

lemma blast_fml_sound:
  assumes "sat_fml w F"
  shows "sat_fml w (blast_fml F,[])"
  unfolding blast_fml_def sat_fml_def
  apply clarsimp
  using assms blast_xors_sound sat_clauses_def sat_fml_def by blast

definition blast_split_fml :: "fml \<Rightarrow> clause list"
  where "blast_split_fml f = blast_fml (split_fml 1 f)"

lemma blast_split_fml_sols:
  assumes "sols (blast_split_fml F,[]) = {}"
  shows "sols F = {}"
  by (metis Collect_empty_eq assms blast_fml_sound blast_split_fml_def sols_def split_fml_sols)

definition certcheck_blast::"
  (clause list \<Rightarrow> bool) \<Rightarrow>
  fml \<Rightarrow> nat list \<Rightarrow>
  real \<Rightarrow> real \<Rightarrow>
  ((nat \<Rightarrow> bool) list \<times>
    (nat \<Rightarrow> (nat \<times> (nat \<Rightarrow> bool) list \<times> (nat \<Rightarrow> bool) list))) \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> (bool list \<times> bool)) \<Rightarrow>
  String.literal + nat"
  where "certcheck_blast check_unsat F S \<epsilon> \<delta> m0ms =
   certcheck (check_unsat \<circ> blast_split_fml) F S \<epsilon> \<delta> m0ms"

(* Just for completeness, we re-state the main theorems *)
corollary certcheck_blast_sound:
  assumes "\<And>F. check_unsat F \<Longrightarrow> sols (F, []) = {}"
  assumes "0 < \<delta>" "\<delta> < 1"
  assumes "0 < \<epsilon>"
  assumes "distinct S"
  shows "
  measure_pmf.prob
    (map_pmf (\<lambda>r. certcheck_blast check_unsat F S \<epsilon> \<delta> (f r) r)
      (random_seed_xors (find_t \<delta>) (length S)))
  {c. \<not> isl c \<and>
     real (projr c) \<notin>
      {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
        (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<le> \<delta>"
  unfolding certcheck_blast_def
  apply (intro CertCheck_CNF_XOR.certcheck_sound[OF _ assms(2-5)])
  using assms(1) unfolding Let_def
  using blast_split_fml_sols by auto

corollary certcheck_blast_promise_complete:
  assumes "\<And>F. check_unsat F \<Longrightarrow> sols (F, []) = {}"
  assumes "0 < \<delta>" "\<delta> < 1"
  assumes "0 < \<epsilon>"
  assumes "distinct S"
  assumes r: "\<And>r.
    r \<in> set_pmf (random_seed_xors (find_t \<delta>) (length S)) \<Longrightarrow>
    \<not>isl (certcheck_blast check_unsat F S \<epsilon> \<delta> (f r) r)"
  shows "
    measure_pmf.prob
      (map_pmf (\<lambda>r. certcheck_blast check_unsat F S \<epsilon> \<delta> (f r) r)
        (random_seed_xors (find_t \<delta>) (length S)))
      {c. real (projr c) \<in>
        {real (card (proj (set S) (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj (set S) (sols F)))}} \<ge> 1 - \<delta>"
  unfolding certcheck_blast_def
  apply (intro CertCheck_CNF_XOR.certcheck_promise_complete[OF _ assms(2-5)])
  using assms(1) unfolding Let_def
  using blast_split_fml_sols assms(6) unfolding certcheck_blast_def by auto

subsection \<open> Export code for a SML implementation. \<close>

definition real_of_int :: "integer \<Rightarrow> real"
  where "real_of_int n = real (nat_of_integer n)"

definition real_mult :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_mult n m = n * m"

definition real_div :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_div n m = n / m"

definition real_plus :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_plus n m = n + m"

definition real_minus :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_minus n m = n - m"

declare [[code abort: fix_t]]

(* Sample code export.
  Helper Isabelle converters, followed by exporting the actual code *)
export_code
  length
  nat_of_integer int_of_integer
  integer_of_nat integer_of_int
  real_of_int real_mult real_div real_plus real_minus
  quotient_of

  Pos Neg
  CertCheck_CNF_XOR.appmc.compute_thresh
  find_t certcheck
  certcheck_blast
  in SML

end
