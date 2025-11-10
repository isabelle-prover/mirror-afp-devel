section \<open>Preliminaries\<close>

theory Term_Context
  imports 
    First_Order_Terms.Subterm_and_Context
    First_Order_Terms.Term_More
    Polynomial_Factorization.Missing_List
begin

subsection \<open>Additional functionality on @{type term} and @{type ctxt}\<close>
 
fun replace_term_at (\<open>_[_ \<leftarrow> _]\<close> [1000, 0, 0] 1000) where
  "replace_term_at s [] t = t"
| "replace_term_at (Var x) ps t = (Var x)"
| "replace_term_at (Fun f ts) (i # ps) t =
    (if i < length ts then Fun f (ts[i:=(replace_term_at (ts ! i) ps t)]) else Fun f ts)"

fun fun_at :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f + 'v) option" where
  "fun_at (Var x) [] = Some (Inr x)"
| "fun_at (Fun f ts) [] = Some (Inl f)"
| "fun_at (Fun f ts) (i # p) = (if i < length ts then fun_at (ts ! i) p else None)"
| "fun_at _ _ = None"


subsubsection \<open>Type conversion\<close>

text \<open>We require a function which adapts the type of variables of a term,
   so that states of the automaton and variables in the term language can be
   chosen independently.\<close>
abbreviation "map_both f \<equiv> map_prod f f"

definition adapt_vars :: "('f, 'q) term \<Rightarrow> ('f,'v)term" where 
  "adapt_vars \<equiv> map_vars_term (\<lambda>_. undefined)"

definition adapt_vars_ctxt :: "('f,'q)ctxt \<Rightarrow> ('f,'v)ctxt" where
  "adapt_vars_ctxt = map_vars_ctxt (\<lambda>_. undefined)"


subsection \<open>Properties on signature induced by a term @{type term}/context @{type ctxt}\<close>

lemma funas_term_map [simp]:
  "funas_term (map_term f h t) = (\<lambda> (g, n). (f g, n)) ` funas_term t"
  by (induct t) auto

lemma ctxt_comp_n_funas [simp]:
  "(f, v) \<in> funas_ctxt (C^n) \<Longrightarrow> (f, v) \<in> funas_ctxt C"
  by (induct n arbitrary: C) auto

lemma ctxt_comp_n_pres_funas [intro]:
  "funas_ctxt C \<subseteq> \<F> \<Longrightarrow> funas_ctxt (C^n) \<subseteq> \<F>"
  by (induct n arbitrary: C) auto

subsection \<open>Properties on subterm at given position @{const subt_at}\<close>

lemma subt_at_Cons_comp:
  "i # p \<in> poss s \<Longrightarrow> (s |_ [i]) |_ p = s |_ (i # p)"
  by (metis subt_at_Cons_distr subt_at.simps(1))

lemma subst_at_ctxt_of_pos_term_eq_termD:
  assumes "s = t" "p \<in> poss t"
  shows "s |_ p = t |_ p \<and> ctxt_of_pos_term p s = ctxt_of_pos_term p t" using assms
  by auto

lemma subst_at_ctxt_at_eq_termI:
  assumes "p \<in> poss s" "p \<in> poss t"
    and "s |_p = t |_ p"
    and "ctxt_of_pos_term p s = ctxt_of_pos_term p t"
  shows "s = t" using assms 
  by (metis ctxt_supt_id)


lemma subt_at_subterm [intro!]:
  "p \<in> poss t \<Longrightarrow> p \<noteq> [] \<Longrightarrow>  t \<rhd> t |_ p"
  using subt_at_id_imp_eps subt_at_imp_supteq subterm.order.not_eq_order_implies_strict by blast


subsection \<open>Properties on replace terms at a given position
  @{const replace_term_at}\<close>

lemma replace_term_at_not_poss [simp]:
  "p \<notin> poss s \<Longrightarrow> s[p \<leftarrow> t] = s"
proof (induct s arbitrary: p)
  case (Var x) then show ?case by (cases p) auto
next
  case (Fun f ts) show ?case using Fun(1)[OF nth_mem] Fun(2)
    by (cases p) (auto simp: min_def intro!: nth_equalityI)
qed

lemma replace_term_at_replace_at_conv:
  "p \<in> poss s \<Longrightarrow> replace_at s p t = s[p \<leftarrow> t]"
  by (induct s arbitrary: p) (auto simp: upd_conv_take_nth_drop)

lemma parallel_replace_term_commute [ac_simps]:
  "p \<bottom> q \<Longrightarrow> s[p \<leftarrow> t][q \<leftarrow> u] = s[q \<leftarrow> u][p \<leftarrow> t]"
proof (induct s arbitrary: p q)
  case (Var x) then show ?case
    by (cases p; cases q) auto
next
  case (Fun f ts)
  from Fun(2) have "p \<noteq> []" "q \<noteq> []" by auto
  then obtain i j ps qs where [simp]: "p = i # ps" "q = j # qs"
    by (cases p; cases q) auto
  have "i \<noteq> j \<Longrightarrow> (Fun f ts)[p \<leftarrow> t][q \<leftarrow> u] = (Fun f ts)[q \<leftarrow> u][p \<leftarrow> t]"
    by (auto simp: list_update_swap)
  then show ?case using Fun(1)[OF nth_mem, of j ps qs] Fun(2)
    by (cases "i = j") auto
qed

lemma replace_term_at_above [simp]:
  "p \<le>\<^sub>p q \<Longrightarrow> s[q \<leftarrow> t][p \<leftarrow> u] = s[p \<leftarrow> u]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "tl q" "args s ! i"] Cons(2)
    by (cases q; cases s) auto
qed auto

lemma replace_term_at_below [simp]:
  "p <\<^sub>p q \<Longrightarrow> s[p \<leftarrow> t][q \<leftarrow> u] = s[p \<leftarrow> t[q -\<^sub>p p \<leftarrow> u]]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "tl q" "args s ! i"] Cons(2)
    by (cases q; cases s) auto
qed auto

lemma replace_at_hole_pos [simp]: "C\<langle>s\<rangle>[hole_pos C \<leftarrow> t] = C\<langle>t\<rangle>"
  by (induct C) auto

subsection \<open>Properties on @{const adapt_vars} and @{const adapt_vars_ctxt}\<close>

lemma adapt_vars2:
  "adapt_vars (adapt_vars t) = adapt_vars t"
  by (induct t) (auto simp add: adapt_vars_def)

lemma adapt_vars_simps[code, simp]: "adapt_vars (Fun f ts) = Fun f (map adapt_vars ts)"
  by (induct ts, auto simp: adapt_vars_def)

lemma adapt_vars_reverse: "ground t \<Longrightarrow> adapt_vars t' = t \<Longrightarrow> adapt_vars t = t'"
  unfolding adapt_vars_def 
proof (induct t arbitrary: t')
  case (Fun f ts)
  then show ?case by (cases t') (auto simp add: map_idI)
qed auto

lemma ground_adapt_vars [simp]: "ground (adapt_vars t) = ground t"
  by (simp add: adapt_vars_def)
lemma funas_term_adapt_vars[simp]: "funas_term (adapt_vars t) = funas_term t" by (simp add: adapt_vars_def)

lemma adapt_vars_adapt_vars[simp]: fixes t :: "('f,'v)term"
  assumes g: "ground t"
  shows "adapt_vars (adapt_vars t :: ('f,'w)term) = t"
proof -
  let ?t' = "adapt_vars t :: ('f,'w)term"
  have gt': "ground ?t'" using g by auto
  from adapt_vars_reverse[OF gt', of t] show ?thesis by blast
qed

lemma adapt_vars_inj:
  assumes "adapt_vars x = adapt_vars y" "ground x" "ground y"
  shows "x = y"
  using adapt_vars_adapt_vars assms by metis

lemma adapt_vars_ctxt_simps[simp, code]: 
  "adapt_vars_ctxt Hole = Hole"
  "adapt_vars_ctxt (More f bef C aft) = More f (map adapt_vars bef) (adapt_vars_ctxt C) (map adapt_vars aft)"
  by (simp_all add: adapt_vars_ctxt_def adapt_vars_def)

lemma adapt_vars_ctxt[simp]: "adapt_vars (C \<langle> t \<rangle> ) = (adapt_vars_ctxt C) \<langle> adapt_vars t \<rangle>"
  by (induct C, auto)

lemma adapt_vars_subst[simp]: "adapt_vars (l \<cdot> \<sigma>) = l \<cdot> (\<lambda> x. adapt_vars (\<sigma> x))"
  unfolding adapt_vars_def
  by (induct l) auto

lemma adapt_vars_gr_map_vars [simp]:
  "ground t \<Longrightarrow> map_vars_term f t = adapt_vars t"
  by (induct t) auto

lemma adapt_vars_gr_ctxt_of_map_vars [simp]:
  "ground_ctxt C \<Longrightarrow> map_vars_ctxt f C = adapt_vars_ctxt C"
  by (induct C) auto

subsubsection \<open>Equality on ground terms/contexts by positions and symbols\<close>

lemma fun_at_def':
  "fun_at t p = (if p \<in> poss t then
    (case t |_ p of Var x \<Rightarrow> Some (Inr x) | Fun f ts \<Rightarrow> Some (Inl f)) else None)"
  by (induct t p rule: fun_at.induct) auto

lemma fun_at_None_nposs_iff:
  "fun_at t p = None \<longleftrightarrow> p \<notin> poss t"
  by (auto simp: fun_at_def') (meson term.case_eq_if)

lemma eq_term_by_poss_fun_at:
  assumes "poss s = poss t" "\<And>p. p \<in> poss s \<Longrightarrow> fun_at s p = fun_at t p"
  shows "s = t"
  using assms
proof (induct s arbitrary: t)
  case (Var x) then show ?case
    by (cases t) simp_all
next
  case (Fun f ss) note Fun' = this
  show ?case
  proof (cases t)
    case (Var x) show ?thesis using Fun'(3)[of "[]"] by (simp add: Var)
  next
    case (Fun g ts)
    have *: "length ss = length ts"
      using Fun'(3) arg_cong[OF Fun'(2), of "\<lambda>P. card {i |i p. i # p \<in> P}"] 
      by (auto simp: Fun exI[of "\<lambda>x. x \<in> poss _", OF empty_pos_in_poss])
    then have "i < length ss \<Longrightarrow> poss (ss ! i) = poss (ts ! i)" for i
      using arg_cong[OF Fun'(2), of "\<lambda>P. {p. i # p \<in> P}"] by (auto simp: Fun)
    then show ?thesis using * Fun'(2) Fun'(3)[of "[]"] Fun'(3)[of "_ # _ :: pos"]
      by (auto simp: Fun intro!: nth_equalityI Fun'(1)[OF nth_mem, of n "ts ! n" for n])
  qed
qed

lemma eq_ctxt_at_pos_by_poss:
  assumes "p \<in> poss s" "p \<in> poss t"
    and "\<And> q. \<not> (p \<le>\<^sub>p q) \<Longrightarrow> q \<in> poss s \<longleftrightarrow> q \<in> poss t"
    and "(\<And> q. q \<in> poss s \<Longrightarrow> \<not> (p \<le>\<^sub>p q) \<Longrightarrow> fun_at s q = fun_at t q)"
  shows "ctxt_of_pos_term p s = ctxt_of_pos_term p t" using assms
proof (induct p arbitrary: s t)
  case (Cons i p)
  from Cons(2, 3) Cons(4, 5)[of "[]"] obtain f ss ts where [simp]: "s = Fun f ss" "t = Fun f ts"
    by (cases s; cases t) auto
  have flt: "j < i \<Longrightarrow> j # q \<in> poss s \<Longrightarrow> fun_at s (j # q) = fun_at t (j # q)" for j q
    by (intro Cons(5)) auto
  have fgt: "i < j \<Longrightarrow> j # q \<in> poss s \<Longrightarrow> fun_at s (j # q) = fun_at t (j # q)" for j q
    by (intro Cons(5)) auto
  have lt: "j < i \<Longrightarrow> j # q \<in> poss s \<longleftrightarrow> j # q \<in> poss t" for j q by (intro Cons(4)) auto
  have gt: "i < j \<Longrightarrow> j # q \<in> poss s \<longleftrightarrow> j # q \<in> poss t" for j q by (intro Cons(4)) auto
  from this[of _ "[]"] have "i < j \<Longrightarrow> j < length ss \<longleftrightarrow> j < length ts" for j by auto
  from this Cons(2, 3) have l: "length ss = length ts" by auto (meson nat_neq_iff)
  have "ctxt_of_pos_term p (ss ! i) = ctxt_of_pos_term p (ts ! i)" using Cons(2, 3) Cons(4-)[of "i # q" for q] 
    by (intro Cons(1)[of "ss ! i" "ts ! i"]) auto
  moreover have "take i ss = take i ts" using l lt Cons(2, 3) flt
    by (intro nth_equalityI) (auto intro!: eq_term_by_poss_fun_at)
  moreover have "drop (Suc i) ss = drop (Suc i) ts" using l Cons(2, 3) fgt gt[of "Suc i + j" for j]
    by (intro nth_equalityI) (auto simp: nth_map intro!: eq_term_by_poss_fun_at, fastforce+)
  ultimately show ?case by auto
qed auto


subsection \<open>Misc\<close>

lemma fun_at_hole_pos_ctxt_apply [simp]:
  "fun_at C\<langle>t\<rangle> (hole_pos C) = fun_at t []"
  by (induct C) auto

lemma map_term_replace_at_dist:
  "p \<in> poss s \<Longrightarrow> (map_term f g s)[p \<leftarrow> (map_term f g t)] = map_term f g (s[p \<leftarrow> t])"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) (auto simp: nth_list_update intro!: nth_equalityI)
qed auto

end
