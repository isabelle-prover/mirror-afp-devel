section \<open>Preliminaries\<close>
theory Terms_Positions
  imports Regular_Tree_Relations.Ground_Terms
begin

subsection \<open>Additional operations on terms and positions\<close>

subsubsection \<open>Linearity\<close>
fun linear_term :: "('f, 'v) term \<Rightarrow> bool" where
  "linear_term (Var _) = True" |
  "linear_term (Fun _ ts) = (is_partition (map vars_term ts) \<and> (\<forall>t\<in>set ts. linear_term t))"
abbreviation "linear_sys \<R> \<equiv> \<forall> (l, r) \<in> \<R>. linear_term l \<and> linear_term r"

subsubsection \<open>Positions induced by contexts, by variables and by given subterms\<close>

definition "possc C = {p | p t. p \<in> poss C\<langle>t\<rangle>}"
definition "varposs s = {p | p. p \<in> poss s \<and> is_Var (s |_ p)}"
definition "poss_of_term u t = {p. p \<in> poss t \<and> t |_ p = u}"


subsubsection \<open>Replacing functions symbols that aren't specified in the signature by variables\<close>

definition "funas_rel \<R> = (\<Union> (l, r) \<in> \<R>. funas_term l \<union> funas_term r)"

fun term_to_sig where
  "term_to_sig \<F> v (Var x) = Var x"
| "term_to_sig \<F> v (Fun f ts) =
    (if (f, length ts) \<in> \<F> then Fun f (map (term_to_sig \<F> v) ts) else Var v)"

fun ctxt_well_def_hole_path where
  "ctxt_well_def_hole_path \<F> Hole \<longleftrightarrow> True"
| "ctxt_well_def_hole_path \<F> (More f ss C ts) \<longleftrightarrow> (f, Suc (length ss + length ts)) \<in> \<F> \<and> ctxt_well_def_hole_path \<F> C"

fun inv_const_ctxt where
  "inv_const_ctxt \<F> v Hole = Hole"
| "inv_const_ctxt \<F> v ((More f ss C ts)) 
              = (More f (map (term_to_sig \<F> v) ss) (inv_const_ctxt \<F> v C) (map (term_to_sig \<F> v) ts))"

fun inv_const_ctxt' where
  "inv_const_ctxt' \<F> v Hole = Var v"
| "inv_const_ctxt' \<F> v ((More f ss C ts)) 
              = (if (f, Suc (length ss + length ts)) \<in> \<F> then Fun f (map (term_to_sig \<F> v) ss @ inv_const_ctxt' \<F> v C # map (term_to_sig \<F> v) ts) else Var v)"


subsubsection \<open>Replace term at a given position in contexts\<close>

fun replace_term_context_at :: "('f, 'v) ctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ctxt"
  ("_[_ \<leftarrow> _]\<^sub>C" [1000, 0] 1000) where
  "replace_term_context_at \<box> p u = \<box>"
| "replace_term_context_at (More f ss C ts) (i # ps) u =
    (if i < length ss then More f (ss[i := (ss ! i)[ps \<leftarrow> u]]) C ts
     else if i = length ss then More f ss (replace_term_context_at C ps u) ts
     else More f ss C (ts[(i - Suc (length ss)) := (ts ! (i - Suc (length ss)))[ps \<leftarrow> u]]))"

abbreviation "constT c \<equiv> Fun c []"

subsubsection \<open>Multihole context closure of a term relation as inductive set\<close>

definition all_ctxt_closed where
  "all_ctxt_closed F r \<longleftrightarrow> (\<forall>f ts ss. (f, length ss) \<in> F \<longrightarrow> length ts = length ss \<longrightarrow>
    (\<forall>i. i < length ts \<longrightarrow> (ts ! i, ss ! i) \<in> r) \<longrightarrow>
    (\<forall> i. i < length ts \<longrightarrow> funas_term (ts ! i) \<union> funas_term (ss ! i) \<subseteq> F) \<longrightarrow> (Fun f ts, Fun f ss) \<in> r) \<and>
    (\<forall> x. (Var x, Var x) \<in> r)"



subsection \<open>Destruction and introduction of @{const all_ctxt_closed}\<close>

lemma all_ctxt_closedD: "all_ctxt_closed F r \<Longrightarrow> (f,length ss) \<in> F \<Longrightarrow> length ts = length ss
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ts ! i, ss ! i) \<in> r \<rbrakk>
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> funas_term (ts ! i) \<subseteq> F \<rbrakk>
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> funas_term (ss ! i) \<subseteq> F \<rbrakk>
  \<Longrightarrow> (Fun f ts, Fun f ss) \<in> r"
  unfolding all_ctxt_closed_def by auto

lemma trans_ctxt_sig_imp_all_ctxt_closed: assumes tran: "trans r"
  and refl: "\<And> t. funas_term t \<subseteq> F \<Longrightarrow> (t,t) \<in> r"
  and ctxt: "\<And> C s t. funas_ctxt C \<subseteq> F \<Longrightarrow> funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow> (s,t) \<in> r \<Longrightarrow> (C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> r"
  shows "all_ctxt_closed F r" unfolding all_ctxt_closed_def
proof (rule, intro allI impI)
  fix f ts ss
  assume f: "(f,length ss) \<in> F" and
         l: "length ts = length ss" and
         steps: "\<forall> i < length ts. (ts ! i, ss ! i) \<in> r" and
         sig: "\<forall> i < length ts. funas_term (ts ! i) \<union>  funas_term (ss ! i) \<subseteq> F"
  from sig have sig_ts: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"  unfolding set_conv_nth by auto
  let ?p = "\<lambda> ss. (Fun f ts, Fun f ss) \<in> r \<and> funas_term (Fun f ss) \<subseteq> F"
  let ?r = "\<lambda> xsi ysi. (xsi, ysi) \<in> r \<and> funas_term ysi \<subseteq> F"
  have init: "?p ts" by (rule conjI[OF refl], insert f sig_ts l, auto)
  have "?p ss"
  proof (rule parallel_list_update[where p = ?p and r = ?r, OF _ HOL.refl init l[symmetric]])
    fix xs i y
    assume len: "length xs = length ts"
       and i: "i < length ts"
       and r: "?r (xs ! i) y"
       and p: "?p xs"
    let ?C = "More f (take i xs) Hole (drop (Suc i) xs)"
    have id1: "Fun f xs = ?C \<langle> xs ! i\<rangle>" using id_take_nth_drop[OF i[folded len]] by simp
    have id2: "Fun f (xs[i := y]) = ?C \<langle> y \<rangle>" using upd_conv_take_nth_drop[OF i[folded len]] by simp
    from p[unfolded id1] have C: "funas_ctxt ?C \<subseteq> F" and xi: "funas_term (xs ! i) \<subseteq> F" by auto
    from r have "funas_term y \<subseteq> F" "(xs ! i, y) \<in> r" by auto
    with ctxt[OF C xi this] C have r: "(Fun f xs, Fun f (xs[i := y])) \<in> r"
      and f: "funas_term (Fun f (xs[i := y])) \<subseteq> F" unfolding id1 id2 by auto
    from p r tran have "(Fun f ts, Fun f (xs[i := y])) \<in> r" unfolding trans_def by auto
    with f
    show "?p (xs[i := y])"  by auto
  qed (insert sig steps, auto)
  then show "(Fun f ts, Fun f ss) \<in> r" ..
qed (insert refl, auto)



subsection \<open>Lemmas for @{const poss} and ordering of positions\<close>

lemma subst_poss_mono: "poss s \<subseteq> poss (s \<cdot> \<sigma>)"
  by (induct s) force+

lemma par_pos_prefix [simp]:
  "(i # p) \<bottom> (i # q) \<Longrightarrow> p \<bottom> q"
  by (simp add: par_Cons_iff)

lemma pos_diff_itself [simp]: "p -\<^sub>p p = []"
  by (simp add: pos_diff_def)

lemma pos_les_eq_append_diff [simp]:
  "p \<le>\<^sub>p q \<Longrightarrow> p @ (q -\<^sub>p p) = q"
  by (metis option.sel pos_diff_def position_less_eq_def remove_prefix_append)

lemma pos_diff_append_itself [simp]: "(p @ q) -\<^sub>p p = q"
  by (simp add: pos_diff_def remove_prefix_append)

lemma poss_pos_diffI:
  "p \<le>\<^sub>p q \<Longrightarrow> q \<in> poss s \<Longrightarrow> q -\<^sub>p p \<in> poss (s |_ p)"
  using poss_append_poss by fastforce

lemma less_eq_poss_append_itself [simp]: "p \<le>\<^sub>p (p @ q)"
  using position_less_eq_def by blast

lemma poss_ctxt_apply [simp]:
  "hole_pos C @ p \<in> poss C\<langle>s\<rangle> \<longleftrightarrow> p \<in> poss s"
  by (induct C) auto

lemma pos_replace_at_pres:
  "p \<in> poss s \<Longrightarrow> p \<in> poss s[p \<leftarrow> t]"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    by (cases s) auto
qed auto

lemma par_pos_replace_pres:
  "p \<in> poss s \<Longrightarrow> p \<bottom> q \<Longrightarrow> p \<in> poss s[q \<leftarrow> t]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) (auto simp add: nth_list_update par_Cons_iff)
qed auto

lemma poss_of_termE [elim]:
  assumes "p \<in> poss_of_term u s"
    and "p \<in> poss s \<Longrightarrow> s |_ p = u \<Longrightarrow> P"
  shows "P" using assms unfolding poss_of_term_def
  by blast

lemma poss_of_term_Cons:
  "i # p \<in> poss_of_term u (Fun f ts) \<Longrightarrow> p \<in> poss_of_term u (ts ! i)"
  unfolding poss_of_term_def by auto

lemma poss_of_term_const_ctxt_apply:
  assumes "p \<in> poss_of_term (constT c) C\<langle>s\<rangle>"
  shows "p \<bottom> (hole_pos C) \<or> (hole_pos C) \<le>\<^sub>p p" using assms
proof (induct p arbitrary: C)
  case Nil then show ?case
    by (cases C) auto
next
  case (Cons i p) then show ?case
    by (cases C) (fastforce simp add: par_Cons_iff dest!: poss_of_term_Cons)+
qed


subsection \<open>Lemmas for @{const subt_at} and @{const replace_term_at}\<close>

lemma subt_at_append_dist:
  "p @ q \<in> poss s \<Longrightarrow> s |_ (p @ q) = (s |_ p) |_ q"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) auto
qed auto

lemma ctxt_apply_term_subt_at_hole_pos [simp]:
  "C\<langle>s\<rangle> |_ (hole_pos C @ q) = s |_ q"
  by (induct C) auto

lemma subst_subt_at_dist:
  "p \<in> poss s \<Longrightarrow> s \<cdot> \<sigma> |_ p = s |_ p \<cdot> \<sigma>"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) auto
qed auto

lemma replace_term_at_subt_at_id [simp]: "s[p \<leftarrow> (s |_ p)] = s"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) auto
qed auto


lemma replace_term_at_same_pos [simp]:
  "s[p \<leftarrow> u][p \<leftarrow> t] = s[p \<leftarrow> t]"
  using position_less_refl replace_term_at_above by blast

\<comment> \<open>Replacement at under substitution\<close>
lemma subt_at_vars_term:
  "p \<in> poss s \<Longrightarrow> s |_ p = Var x \<Longrightarrow> x \<in> vars_term s"
  by (metis UnCI ctxt_at_pos_subt_at_id term.set_intros(3) vars_term_ctxt_apply)

lemma linear_term_varposs_subst_replace_term:
  "linear_term s \<Longrightarrow> p \<in> varposs s \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow>
     (s \<cdot> \<sigma>)[q \<leftarrow> u] = s \<cdot> (\<lambda> x. if Var x = s |_ p then (\<sigma> x)[q -\<^sub>p p \<leftarrow> u] else (\<sigma> x))"
proof (induct q arbitrary: s p)
  case (Cons i q)
  show ?case using Cons(1)[of "args s ! i" "tl p"] Cons(2-)
    by (cases s) (auto simp: varposs_def nth_list_update term_subst_eq_conv
      is_partition_alt is_partition_alt_def disjoint_iff subt_at_vars_term intro!: nth_equalityI)
qed (auto simp: varposs_def)

\<comment> \<open>Replacement at context parallel to the hole position\<close>
lemma par_hole_pos_replace_term_context_at:
  "p \<bottom> hole_pos C \<Longrightarrow> C\<langle>s\<rangle>[p \<leftarrow> u] = (C[p \<leftarrow> u]\<^sub>C)\<langle>s\<rangle>"
proof (induct p arbitrary: C)
  case (Cons i p)
  from Cons(2) obtain f ss D ts where [simp]: "C = More f ss D ts" by (cases C) auto 
  show ?case using Cons(1)[of D] Cons(2)
    by (auto simp: list_update_append nth_append_Cons minus_nat.simps(2) split: nat.splits)
qed auto

lemma par_pos_replace_term_at:
  "p \<in> poss s \<Longrightarrow> p \<bottom> q \<Longrightarrow> s[q \<leftarrow> t] |_ p = s |_ p"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) (auto, metis nth_list_update par_Cons_iff)
qed auto


lemma less_eq_subt_at_replace:
  "p \<in> poss s \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow> s[q \<leftarrow> t] |_ p = (s |_ p)[q -\<^sub>p p \<leftarrow> t]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) auto
qed auto


lemma greater_eq_subt_at_replace:
  "p \<in> poss s \<Longrightarrow> q \<le>\<^sub>p p \<Longrightarrow> s[q \<leftarrow> t] |_ p = t |_ (p -\<^sub>p q)"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) auto
qed auto

lemma replace_subterm_at_itself [simp]:
  "s[p \<leftarrow> (s |_ p)[q \<leftarrow> t]] = s[p @ q \<leftarrow> t]"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"]
    by (cases s) auto
qed auto


lemma hole_pos_replace_term_at [simp]:
  "hole_pos C \<le>\<^sub>p p \<Longrightarrow> C\<langle>s\<rangle>[p \<leftarrow> u] = C\<langle>s[p -\<^sub>p hole_pos C \<leftarrow> u]\<rangle>"
proof (induct C arbitrary: p)
  case (More f ss C ts) then show ?case
    by (cases p) auto
qed auto

lemma ctxt_of_pos_term_apply_replace_at_ident:
  assumes "p \<in> poss s"
  shows "(ctxt_at_pos s p)\<langle>t\<rangle> = s[p \<leftarrow> t]"
  using assms
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    by (cases s) (auto simp: nth_append_Cons intro!: nth_equalityI)
qed auto

lemma ctxt_apply_term_replace_term_hole_pos [simp]:
  "C\<langle>s\<rangle>[hole_pos C @ q  \<leftarrow> u] = C\<langle>s[q  \<leftarrow> u]\<rangle>"
  by (simp add: pos_diff_def position_less_eq_def remove_prefix_append)

lemma ctxt_apply_subt_at_hole_pos [simp]: "C\<langle>s\<rangle> |_ hole_pos C = s"
  by (induct C) auto

lemma subt_at_imp_supteq':
  assumes "p \<in> poss s" and "s|_p = t" shows "s \<unrhd> t" using assms
proof (induct p arbitrary: s)
  case (Cons i p)
  from Cons(2-) show ?case using Cons(1)[of "args s ! i"]
    by (cases s) force+
qed auto

lemma subt_at_imp_supteq:
  assumes "p \<in> poss s" shows "s \<unrhd> s|_p"
proof -
 have "s|_p = s|_p" by auto
 with assms show ?thesis by (rule subt_at_imp_supteq')
qed


subsection \<open>@{const term_to_sig} invariants and distributions\<close>

lemma fuans_term_term_to_sig [simp]: "funas_term (term_to_sig \<F> v t) \<subseteq> \<F>"
  by (induct t) auto

lemma term_to_sig_id [simp]:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> term_to_sig \<F> v t = t"
  by (induct t) (auto simp add: UN_subset_iff map_idI)

lemma term_to_sig_subst_sig [simp]:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> term_to_sig \<F> v (t \<cdot> \<sigma>) = t \<cdot> (\<lambda> x.  term_to_sig \<F> v (\<sigma> x))"
  by (induct t) auto

lemma funas_ctxt_ctxt_inv_const_ctxt_ind [simp]:
  "funas_ctxt C \<subseteq> \<F> \<Longrightarrow> inv_const_ctxt \<F> v C = C"
  by (induct C) (auto simp add: UN_subset_iff intro!: nth_equalityI)

lemma term_to_sig_ctxt_apply [simp]:
  "ctxt_well_def_hole_path \<F> C \<Longrightarrow> term_to_sig \<F> v C\<langle>s\<rangle> = (inv_const_ctxt \<F> v C)\<langle>term_to_sig \<F> v s\<rangle>"
  by (induct C) auto

lemma term_to_sig_ctxt_apply' [simp]:
  "\<not> ctxt_well_def_hole_path \<F> C \<Longrightarrow> term_to_sig \<F> v C\<langle>s\<rangle> = inv_const_ctxt' \<F> v C"
  by (induct C) auto

lemma funas_ctxt_ctxt_well_def_hole_path:
  "funas_ctxt C \<subseteq> \<F> \<Longrightarrow> ctxt_well_def_hole_path \<F> C"
  by (induct C) auto


subsection \<open>Misc\<close>

lemma funas_term_subt_at:
  "(f, n) \<in> funas_term t \<Longrightarrow> (\<exists> p ts. p \<in> poss t \<and> t |_ p = Fun f ts \<and> length ts = n)"
proof (induct t)
  case (Fun g ts) note IH = this
  show ?case
  proof (cases "g = f \<and> length ts = n")
    case False
    then obtain i where i: "i < length ts" "(f, n) \<in> funas_term (ts ! i)" using IH(2)
      using in_set_idx by force
    from IH(1)[OF nth_mem[OF this(1)] this(2)] show ?thesis using i(1)
      by (metis poss_Cons_poss subt_at.simps(2) term.sel(4))
  qed auto
qed simp

lemma finite_poss: "finite (poss s)"
proof (induct s)
  case (Fun f ts)
  have "poss (Fun f ts) = insert [] (\<Union> (set (map2 (\<lambda> i p. ((#) i) ` p) [0..< length ts] (map poss ts))))"
    by (auto simp: image_iff set_zip split: prod.splits)
  then show ?case using Fun
    by (auto simp del: poss.simps dest!: set_zip_rightD)
qed simp

lemma finite_varposs: "finite (varposs s)"
  by (intro finite_subset[of "varposs s" "poss s"]) (auto simp: varposs_def finite_poss)

lemma gound_linear [simp]: "ground t \<Longrightarrow> linear_term t"
  by (induct t) (auto simp: is_partition_alt is_partition_alt_def)

declare ground_substI[intro, simp]
lemma ground_ctxt_substI:
  "(\<And> x. x \<in> vars_ctxt C \<Longrightarrow> ground (\<sigma> x)) \<Longrightarrow> ground_ctxt (C \<cdot>\<^sub>c \<sigma>)"
  by (induct C) auto


lemma funas_ctxt_subst_apply_ctxt:
  "funas_ctxt (C \<cdot>\<^sub>c \<sigma>) = funas_ctxt C \<union> (\<Union> (funas_term ` \<sigma> ` vars_ctxt C))"
proof (induct C)
  case (More f ss C ts)
  then show ?case
    by (fastforce simp add: funas_term_subst)
qed simp

lemma varposs_Var[simp]:
  "varposs (Var x) = {[]}"
  by (auto simp: varposs_def)

lemma varposs_Fun[simp]:
  "varposs (Fun f ts) = { i # p| i p. i < length ts \<and> p \<in> varposs (ts ! i)}"
  by (auto simp: varposs_def)

lemma vars_term_varposs_iff:
  "x \<in> vars_term s \<longleftrightarrow> (\<exists> p \<in> varposs s. s |_ p = Var x)"
proof (induct s)
  case (Fun f ts)
  show ?case using Fun[OF nth_mem]
    by (force simp: in_set_conv_nth Bex_def)
qed auto

lemma vars_term_empty_ground:
  "vars_term s = {} \<Longrightarrow> ground s"
  by (metis equals0D ground_substI subst_ident)

lemma ground_subst_apply: "ground t \<Longrightarrow> t \<cdot> \<sigma> = t"
  by (induct t) (auto intro: nth_equalityI)

lemma varposs_imp_poss:
  "p \<in> varposs s \<Longrightarrow> p \<in> poss s" by (auto simp: varposs_def)

lemma varposs_empty_gound:
 "varposs s = {} \<longleftrightarrow> ground s"
  by (induct s) (fastforce simp: in_set_conv_nth)+

lemma funas_term_subterm_atI [intro]:
  "p \<in> poss s \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term (s |_ p) \<subseteq> \<F>"
  by (metis ctxt_at_pos_subt_at_id funas_ctxt_apply le_sup_iff)

lemma varposs_ground_replace_at:
  "p \<in> varposs s \<Longrightarrow> ground u \<Longrightarrow> varposs s[p \<leftarrow> u] = varposs s - {p}"
proof (induct p arbitrary: s)
  case Nil then show ?case
    by (cases s) (auto simp: varposs_empty_gound)
next
  case (Cons i p)
  from Cons(2) obtain f ts where [simp]: "s = Fun f ts" by (cases s) auto
  from Cons(2) have var: "p \<in> varposs (ts ! i)" by auto
  from Cons(1)[OF var Cons(3)] have "j < length ts \<Longrightarrow> {j # q| q. q \<in> varposs (ts[i := (ts ! i)[p \<leftarrow> u]] ! j)} =
           {j # q |q. q \<in> varposs (ts ! j)} - {i # p}" for j
    by (cases "j = i") (auto simp add: nth_list_update)
  then show ?case by auto blast
qed

lemma funas_term_replace_at_upper:
  "funas_term s[p \<leftarrow> t] \<subseteq> funas_term s \<union> funas_term t"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"]
    by (cases s) (fastforce simp: in_set_conv_nth nth_list_update split!: if_splits)+
qed simp

lemma funas_term_replace_at_lower:
  "p \<in> poss s \<Longrightarrow> funas_term t \<subseteq> funas_term (s[p \<leftarrow> t])"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    by (cases s) (fastforce simp: in_set_conv_nth nth_list_update split!: if_splits)+
qed simp

lemma poss_of_term_possI [intro!]:
  "p \<in> poss s \<Longrightarrow> s |_ p = u \<Longrightarrow> p \<in> poss_of_term u s"
  unfolding poss_of_term_def by blast

lemma poss_of_term_replace_term_at:
  "p \<in> poss s \<Longrightarrow> p \<in> poss_of_term u s[p \<leftarrow> u]"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) (auto simp: poss_of_term_def)
qed auto

lemma constT_nfunas_term_poss_of_term_empty:
  "(c, 0) \<notin> funas_term t \<longleftrightarrow> poss_of_term (constT c) t = {}"
  unfolding poss_of_term_def
  using funas_term_subt_at[of c 0 t]
  using funas_term_subterm_atI[where ?\<F> ="funas_term t" and ?s = t, THEN subsetD]
  by auto

lemma poss_of_term_poss_emptyD:
  assumes "poss_of_term u s = {}"
  shows "p \<in> poss s \<Longrightarrow> s |_ p \<noteq> u" using assms
  unfolding poss_of_term_def by blast

lemma possc_subt_at_ctxt_apply:
  "p \<in> possc C \<Longrightarrow> p \<bottom> hole_pos C \<Longrightarrow> C\<langle>s\<rangle> |_ p = C\<langle>t\<rangle> |_ p"
proof (induct p arbitrary: C)
  case (Cons i p)
  have [dest]: "length ss # p \<in> possc (More f ss D ts) \<Longrightarrow> p \<in> possc D" for f ss D ts
    by (auto simp: possc_def)
  show ?case using Cons
    by (cases C) (auto simp: nth_append_Cons)
qed simp

end