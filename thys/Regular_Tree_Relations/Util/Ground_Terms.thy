subsection \<open>Ground constructions\<close>

theory Ground_Terms
  imports Basic_Utils
begin

subsubsection \<open>Ground terms\<close>

text \<open>This type serves two purposes. First of all, the encoding definitions and proofs are not
littered by cases for variables. Secondly, we can consider tree domains (usually sets of positions),
which become a special case of ground terms. This enables the construction of a term from a
tree domain and a function from positions to symbols.\<close>

datatype 'f gterm =
  GFun (groot_sym: 'f) (gargs: "'f gterm list")

lemma gterm_idx_induct[case_names GFun]:
  assumes "\<And> f ts. (\<And> i. i < length ts \<Longrightarrow> P (ts ! i)) \<Longrightarrow> P (GFun f ts)"
  shows "P t" using assms
  by (induct t) auto

fun term_of_gterm where
  "term_of_gterm (GFun f ts) = Fun f (map term_of_gterm ts)"

fun gterm_of_term where
  "gterm_of_term (Fun f ts) = GFun f (map gterm_of_term ts)"

fun groot where
  "groot (GFun f ts) = (f, length ts)"

lemma groot_sym_groot_conv:
  "groot_sym t = fst (groot t)"
  by (cases t) auto

lemma groot_sym_gterm_of_term:
  "ground t \<Longrightarrow> groot_sym (gterm_of_term t) = fst (the (root t))"
  by (cases t) auto

lemma length_args_length_gargs [simp]:
  "length (args (term_of_gterm t)) = length (gargs t)"
  by (cases t) auto

lemma ground_term_of_gterm [simp]:
  "ground (term_of_gterm s)"
  by (induct s) auto

lemma ground_term_of_gterm' [simp]:
  "term_of_gterm s = Fun f ss \<Longrightarrow> ground (Fun f ss)"
  by (induct s) auto

lemma term_of_gterm_inv [simp]:
  "gterm_of_term (term_of_gterm t) = t"
  by (induct t) (auto intro!: nth_equalityI)

lemma inj_term_of_gterm:
  "inj_on term_of_gterm X"
  by (metis inj_on_def term_of_gterm_inv)

lemma gterm_of_term_inv [simp]:
  "ground t \<Longrightarrow> term_of_gterm (gterm_of_term t) = t"
  by (induct t) (auto 0 0 intro!: nth_equalityI)

lemma ground_term_to_gtermD:
  "ground t \<Longrightarrow> \<exists>t'. t = term_of_gterm t'"
  by (metis gterm_of_term_inv)

lemma map_term_of_gterm [simp]:
  "map_term f g (term_of_gterm t) = term_of_gterm (map_gterm f t)"
  by (induct t) auto

lemma map_gterm_of_term [simp]:
  "ground t \<Longrightarrow> gterm_of_term (map_term f g t) = map_gterm f (gterm_of_term t)"
  by (induct t) auto

lemma gterm_set_gterm_funs_terms:
  "set_gterm t = funs_term (term_of_gterm t)"
  by (induct t) auto

lemma term_set_gterm_funs_terms:
  assumes "ground t"
  shows "set_gterm (gterm_of_term t) = funs_term t"
  using assms by (induct t) auto

lemma vars_term_of_gterm [simp]:
  "vars_term (term_of_gterm t) = {}"
  by (induct t) auto

lemma vars_term_of_gterm_subseteq [simp]:
  "vars_term (term_of_gterm t) \<subseteq> Q \<longleftrightarrow> True"
  by auto

context
  notes conj_cong [fundef_cong]
begin
fun gposs :: "'f gterm \<Rightarrow> pos set" where
  "gposs (GFun f ss) = {[]} \<union> {i # p | i p. i < length ss \<and> p \<in> gposs (ss ! i)}"
end

lemma gposs_Nil [simp]: "[] \<in> gposs s"
  by (cases s) auto

lemma gposs_map_gterm [simp]:
  "gposs (map_gterm f s) = gposs s"
  by (induct s) auto

lemma poss_gposs_conv:
  "poss (term_of_gterm t) = gposs t"
  by (induct t) auto

lemma poss_gposs_mem_conv:
  "p \<in> poss (term_of_gterm t) \<longleftrightarrow> p \<in> gposs t"
  using poss_gposs_conv by auto

lemma gposs_to_poss:
  "p \<in> gposs t \<Longrightarrow> p \<in> poss (term_of_gterm t)"
  by (simp add: poss_gposs_mem_conv)

fun gfun_at :: "'f gterm \<Rightarrow> pos \<Rightarrow> 'f option" where
  "gfun_at (GFun f ts) [] = Some f"
| "gfun_at (GFun f ts) (i # p) = (if i < length ts then gfun_at (ts ! i) p else None)"

abbreviation "exInl \<equiv> case_sum (\<lambda> x. x) (\<lambda> _.undefined)"

lemma gfun_at_gterm_of_term [simp]:
  "ground s \<Longrightarrow> map_option exInl (fun_at s p) = gfun_at (gterm_of_term s) p"
proof (induct p arbitrary: s)
  case Nil then show ?case
    by (cases s) auto
next
  case (Cons i p) then show ?case
    by (cases s) auto
qed

lemmas gfun_at_gterm_of_term' [simp] = gfun_at_gterm_of_term[OF ground_term_of_gterm, unfolded term_of_gterm_inv]

lemma gfun_at_None_ngposs_iff: "gfun_at s p = None \<longleftrightarrow> p \<notin> gposs s"
  by (induct rule: gfun_at.induct) auto


lemma gfun_at_map_gterm [simp]:
  "gfun_at (map_gterm f t) p = map_option f (gfun_at t p)"
  by (induct t arbitrary: p; case_tac p) (auto simp: comp_def)

lemma set_gterm_gposs_conv:
  "set_gterm t = {the (gfun_at t p) | p. p \<in> gposs t}"
proof (induct t)
  case (GFun f ts)
  note [simp] = gfun_at_gterm_of_term[OF ground_term_of_gterm, unfolded term_of_gterm_inv]
  have [simp]: "{the (map_option exInl (fun_at (Fun f (map term_of_gterm ts :: (_, unit) term list)) p)) |p.
    \<exists>i pa. p = i # pa \<and> i < length ts \<and> pa \<in> gposs (ts ! i)} =
    (\<Union>x\<in>{ts ! i |i. i < length ts}. {the (gfun_at x p) |p. p \<in> gposs x})" (* eww *)
    unfolding UNION_eq
  proof ((intro set_eqI iffI; elim CollectE exE bexE conjE), goal_cases lr rl)
    case (lr x p i pa) then show ?case
      by (intro CollectI[of _ x] bexI[of _ "ts ! i"] exI[of _ pa]) (auto intro!: arg_cong[where ?f = the])
  next
    case (rl x xa i p) then show ?case
      by (intro CollectI[of _ x] exI[of _ "i # p"]) auto
  qed
  have [simp]: "(\<Union>x\<in>{ts ! i |i. i < length ts}. {the (gfun_at x p) |p. p \<in> gposs x}) =
    {the (gfun_at (GFun f ts) p) |p. \<exists>i pa. p = i # pa \<and> i < length ts \<and> pa \<in> gposs (ts ! i)}"
    by auto (metis gfun_at.simps(2))+
  show ?case
    by (simp add: GFun(1) set_conv_nth conj_disj_distribL ex_disj_distrib Collect_disj_eq) 
qed

text \<open>A @{type gterm} version of lemma @{verbatim eq_term_by_poss_fun_at}.\<close>

lemma fun_at_gfun_at_conv:
  "fun_at (term_of_gterm s) p = fun_at (term_of_gterm t) p \<longleftrightarrow> gfun_at s p = gfun_at t p"
proof (induct p arbitrary: s t)
  case Nil then show ?case
    by (cases s; cases t) auto
next
  case (Cons i p)
  obtain f h ss ts where [simp]: "s = GFun f ss" "t = GFun h ts" by (cases s; cases t) auto
  have [simp]: "None = fun_at (term_of_gterm (ts ! i)) p \<longleftrightarrow> p \<notin> gposs (ts ! i)"
    using fun_at_None_nposs_iff by (metis poss_gposs_mem_conv)
  have [simp]:"None = gfun_at (ts ! i) p \<longleftrightarrow> p \<notin> gposs (ts ! i)"
    using gfun_at_None_ngposs_iff by force
  show ?case using Cons[of "gargs s ! i" "gargs t ! i"]
    by (auto simp: poss_gposs_conv gfun_at_None_ngposs_iff fun_at_None_nposs_iff
       intro!: iffD2[OF gfun_at_None_ngposs_iff] iffD2[OF fun_at_None_nposs_iff])
qed

lemmas eq_gterm_by_gposs_gfun_at = arg_cong[where f = gterm_of_term,
  OF eq_term_by_poss_fun_at[of "term_of_gterm s :: (_, unit) term" "term_of_gterm t :: (_, unit) term" for s t],
  unfolded term_of_gterm_inv poss_gposs_conv fun_at_gfun_at_conv]

fun gsubt_at :: "'f gterm \<Rightarrow> pos \<Rightarrow> 'f gterm" where
  "gsubt_at s [] = s" |
  "gsubt_at (GFun f ss) (i # p) = gsubt_at (ss ! i) p"

lemma gsubt_at_to_subt_at:
  assumes "p \<in> gposs s"
  shows "gterm_of_term (term_of_gterm s |_ p) = gsubt_at s p"
  using assms by (induct arbitrary: p) (auto simp add: map_idI)

lemma term_of_gterm_gsubt:
  assumes "p \<in> gposs s"
  shows "(term_of_gterm s) |_ p = term_of_gterm (gsubt_at s p)"
  using assms by (induct arbitrary: p) auto

lemma gsubt_at_gposs [simp]:
  assumes "p \<in> gposs s"
  shows "gposs (gsubt_at s p) = {x | x. p @ x \<in> gposs s}"
  using assms by (induct s arbitrary: p) auto

lemma gfun_at_gsub_at [simp]:
  assumes "p \<in> gposs s" and "p @ q \<in> gposs s"
  shows "gfun_at (gsubt_at s p) q = gfun_at s (p @ q)"
  using assms by (induct s arbitrary: p q) auto

lemma gposs_gsubst_at_subst_at_eq [simp]:
  assumes "p \<in> gposs s"
  shows "gposs (gsubt_at s p) = poss (term_of_gterm s |_ p)" using assms
proof (induct s arbitrary: p)
  case (GFun f ts)
  show ?case using GFun(1)[OF nth_mem] GFun(2-)
    by (auto simp: poss_gposs_mem_conv) blast+
qed

lemma gpos_append_gposs:
  assumes "p \<in> gposs t" and "q \<in> gposs (gsubt_at t p)"
  shows "p @ q \<in> gposs t"
  using assms by auto


text \<open>Replace terms at position\<close>

fun replace_gterm_at ("_[_ \<leftarrow> _]\<^sub>G" [1000, 0, 0] 1000) where
  "replace_gterm_at s [] t = t"
| "replace_gterm_at (GFun f ts) (i # ps) t =
    (if i < length ts then GFun f (ts[i:=(replace_gterm_at (ts ! i) ps t)]) else GFun f ts)"

lemma replace_gterm_at_not_poss [simp]:
  "p \<notin> gposs s \<Longrightarrow> s[p \<leftarrow> t]\<^sub>G = s"
proof (induct s arbitrary: p)
  case (GFun f ts) show ?case using GFun(1)[OF nth_mem] GFun(2)
    by (cases p) (auto simp: min_def intro!: nth_equalityI)
qed

lemma parallel_replace_gterm_commute [ac_simps]:
  "p \<bottom> q \<Longrightarrow> s[p \<leftarrow> t]\<^sub>G[q \<leftarrow> u]\<^sub>G = s[q \<leftarrow> u]\<^sub>G[p \<leftarrow> t]\<^sub>G"
proof (induct s arbitrary: p q)
  case (GFun f ts)
  from GFun(2) have "p \<noteq> []" "q \<noteq> []" by auto
  then obtain i j ps qs where [simp]: "p = i # ps" "q = j # qs"
    by (cases p; cases q) auto
  have "i \<noteq> j \<Longrightarrow> (GFun f ts)[p \<leftarrow> t]\<^sub>G[q \<leftarrow> u]\<^sub>G = (GFun f ts)[q \<leftarrow> u]\<^sub>G[p \<leftarrow> t]\<^sub>G"
    by (auto simp: list_update_swap)
  then show ?case using GFun(1)[OF nth_mem, of j ps qs] GFun(2)
    by (cases "i = j") (auto simp: par_Cons_iff)
qed

lemma replace_gterm_at_above [simp]:
  "p \<le>\<^sub>p q \<Longrightarrow> s[q \<leftarrow> t]\<^sub>G[p \<leftarrow> u]\<^sub>G = s[p \<leftarrow> u]\<^sub>G"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "tl q" "gargs s ! i"] Cons(2)
    by (cases q; cases s) auto
qed auto

lemma replace_gterm_at_below [simp]:
  "p <\<^sub>p q \<Longrightarrow> s[p \<leftarrow> t]\<^sub>G[q \<leftarrow> u]\<^sub>G = s[p \<leftarrow> t[q -\<^sub>p p \<leftarrow> u]\<^sub>G]\<^sub>G"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "tl q" "gargs s ! i"] Cons(2)
    by (cases q; cases s) auto
qed auto

lemma groot_sym_replace_gterm [simp]:
  "p \<noteq> [] \<Longrightarrow> groot_sym s[p \<leftarrow> t]\<^sub>G = groot_sym s"
  by (cases s; cases p) auto

lemma replace_gterm_gsubt_at_id [simp]: "s[p \<leftarrow> gsubt_at s p]\<^sub>G = s"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) auto
qed auto

lemma replace_gterm_conv:
  "p \<in> gposs s \<Longrightarrow> (term_of_gterm s)[p \<leftarrow> (term_of_gterm t)] = term_of_gterm (s[p \<leftarrow> t]\<^sub>G)"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) (auto simp: nth_list_update intro: nth_equalityI)
qed auto

subsubsection \<open>Tree domains\<close>

type_synonym gdomain = "unit gterm"

abbreviation gdomain where
  "gdomain \<equiv> map_gterm (\<lambda>_. ())"

lemma gdomain_id:
  "gdomain t = t"
proof -
  have [simp]: "(\<lambda>_. ()) = id" by auto
  then show ?thesis by (simp add: gterm.map_id)
qed

lemma gdomain_gsubt [simp]:
  assumes "p \<in> gposs t"
  shows "gdomain (gsubt_at t p) = gsubt_at (gdomain t) p"
  using assms by (induct t arbitrary: p) auto

text \<open>Union of tree domains\<close>

fun gunion :: "gdomain \<Rightarrow> gdomain \<Rightarrow> gdomain" where
  "gunion (GFun f ss) (GFun g ts) = GFun () (map (\<lambda>i.
    if i < length ss then if i < length ts then gunion (ss ! i) (ts ! i)
    else ss ! i else ts ! i) [0..<max (length ss) (length ts)])"

lemma gposs_gunion [simp]:
  "gposs (gunion s t) = gposs s \<union> gposs t"
  by (induct s t rule: gunion.induct) (auto simp: less_max_iff_disj split: if_splits)

lemma gunion_unit [simp]:
  "gunion s (GFun () []) = s" "gunion (GFun () []) s = s"
  by (cases s, (auto intro!: nth_equalityI)[1])+

lemma gunion_gsubt_at_nt_poss1:
  assumes "p \<in> gposs s" and "p \<notin> gposs t"
  shows "gsubt_at (gunion s t) p = gsubt_at s p"
  using assms by (induct s arbitrary: p t) (case_tac p; case_tac t, auto)


lemma gunion_gsubt_at_nt_poss2:
  assumes "p \<in> gposs t" and "p \<notin> gposs s"
  shows "gsubt_at (gunion s t) p = gsubt_at t p"
  using assms by (induct t arbitrary: p s) (case_tac p; case_tac s, auto)

lemma gunion_gsubt_at_poss:
  assumes "p \<in> gposs s" and "p \<in> gposs t"
  shows "gunion (gsubt_at s p) (gsubt_at t p) = gsubt_at (gunion s t) p"
  using assms
proof (induct p arbitrary: s t)
  case (Cons a p)
  then show ?case by (cases s; cases t) auto 
qed auto 

lemma gfun_at_domain:
  shows "gfun_at t p = (if p \<in> gposs t then Some () else None)"
proof (induct t arbitrary: p)
  case (GFun f ts) then show ?case
    by (cases p) auto
qed

lemma gunion_assoc [ac_simps]:
  "gunion s (gunion t u) = gunion (gunion s t) u"
  by (intro eq_gterm_by_gposs_gfun_at) (auto simp: gfun_at_domain poss_gposs_mem_conv)

lemma gunion_commute [ac_simps]:
  "gunion s t = gunion t s"
  by (intro eq_gterm_by_gposs_gfun_at) (auto simp: gfun_at_domain poss_gposs_mem_conv)

lemma gunion_idemp [simp]:
  "gunion s s = s"
  by (intro eq_gterm_by_gposs_gfun_at) (auto simp: gfun_at_domain poss_gposs_mem_conv)

definition gunions :: "gdomain list \<Rightarrow> gdomain" where
  "gunions ts = foldr gunion ts (GFun () [])"

lemma gunions_append:
  "gunions (ss @ ts) = gunion (gunions ss) (gunions ts)"
  by (induct ss) (auto simp: gunions_def gunion_assoc)

lemma gposs_gunions [simp]:
  "gposs (gunions ts) = {[]} \<union> \<Union>{gposs t |t. t \<in> set ts}"
  by (induct ts) (auto simp: gunions_def)


text \<open>Given a tree domain and a function from positions to symbols, we can construct a term.\<close>
context
  notes conj_cong [fundef_cong]
begin
fun glabel :: "(pos \<Rightarrow> 'f) \<Rightarrow> gdomain \<Rightarrow> 'f gterm" where
  "glabel h (GFun f ts) = GFun (h []) (map (\<lambda>i. glabel (h \<circ> (#) i) (ts ! i)) [0..<length ts])"
end

lemma map_gterm_glabel:
  "map_gterm f (glabel h t) = glabel (f \<circ> h) t"
  by (induct t arbitrary: h) (auto simp: comp_def)

lemma gfun_at_glabel [simp]:
  "gfun_at (glabel f t) p = (if p \<in> gposs t then Some (f p) else None)"
  by (induct t arbitrary: f p, case_tac p) (auto simp: comp_def)

lemma gposs_glabel [simp]:
  "gposs (glabel f t) = gposs t"
  by (induct t arbitrary: f) auto

lemma glabel_map_gterm_conv:
  "glabel (f \<circ> gfun_at t) (gdomain t) = map_gterm (f \<circ> Some) t"
  by (induct t) (auto simp: comp_def intro!: nth_equalityI)

lemma gfun_at_nongposs [simp]:
  "p \<notin> gposs t \<Longrightarrow> gfun_at t p = None"
  using gfun_at_glabel[of "the \<circ> gfun_at t" "gdomain t" p, unfolded glabel_map_gterm_conv]
  by (simp add: comp_def option.map_ident)

lemma gfun_at_poss:
  "p \<in> gposs t \<Longrightarrow> \<exists>f. gfun_at t p = Some f"
  using gfun_at_glabel[of "the \<circ> gfun_at t" "gdomain t" p, unfolded glabel_map_gterm_conv]
  by (auto simp: comp_def)

lemma gfun_at_possE:
  assumes "p \<in> gposs t"
  obtains f where "gfun_at t p = Some f"
  using assms gfun_at_poss by blast

lemma gfun_at_poss_gpossD:
  "gfun_at t p = Some f \<Longrightarrow> p \<in> gposs t"
  by (metis gfun_at_nongposs option.distinct(1))

text \<open>function symbols of a ground term\<close>

primrec funas_gterm :: "'f gterm \<Rightarrow> ('f \<times> nat) set" where
  "funas_gterm (GFun f ts) = {(f, length ts)} \<union> \<Union>(set (map funas_gterm ts))"

lemma funas_gterm_gterm_of_term:
  "ground t \<Longrightarrow> funas_gterm (gterm_of_term t) = funas_term t"
  by (induct t) (auto simp: funas_gterm_def)

lemma funas_term_of_gterm_conv:
  "funas_term (term_of_gterm t) = funas_gterm t"
  by (induct t) (auto simp: funas_gterm_def)

lemma funas_gterm_map_gterm:
  assumes "funas_gterm t \<subseteq> \<F>"
  shows "funas_gterm (map_gterm f t) \<subseteq> (\<lambda> (h, n). (f h, n)) ` \<F>"
  using assms by (induct t) (auto simp: funas_gterm_def)

lemma gterm_of_term_inj:
  assumes "\<And> t. t \<in> S \<Longrightarrow> ground t"
  shows "inj_on gterm_of_term S"
  using assms gterm_of_term_inv by (fastforce simp: inj_on_def)

lemma funas_gterm_gsubt_at_subseteq:
  assumes "p \<in> gposs s"
  shows "funas_gterm (gsubt_at s p) \<subseteq> funas_gterm s" using assms
  apply (induct s arbitrary: p) apply auto
  using nth_mem by blast+

lemma finite_funas_gterm: "finite (funas_gterm t)"
  by (induct t) auto

text \<open>ground term set\<close>

abbreviation gterms where
  "gterms \<F> \<equiv> {s. funas_gterm s \<subseteq> \<F>}"

lemma gterms_mono:
  "\<G> \<subseteq> \<F> \<Longrightarrow> gterms \<G> \<subseteq> gterms \<F>"
  by auto

inductive_set \<T>\<^sub>G for \<F> where
  const [simp]: "(a, 0) \<in> \<F> \<Longrightarrow> GFun a [] \<in> \<T>\<^sub>G \<F>"
| ind [intro]: "(f, n) \<in> \<F> \<Longrightarrow> length ss = n \<Longrightarrow> (\<And> i. i < length ss \<Longrightarrow> ss ! i \<in> \<T>\<^sub>G \<F>) \<Longrightarrow> GFun f ss \<in> \<T>\<^sub>G \<F>"

lemma \<T>\<^sub>G_sound:
  "s \<in> \<T>\<^sub>G \<F> \<Longrightarrow> funas_gterm s \<subseteq> \<F>"
proof (induct)
  case (GFun f ts)
  show ?case using GFun(1)[OF nth_mem] GFun(2)
    by (fastforce simp: in_set_conv_nth elim!: \<T>\<^sub>G.cases intro: nth_mem)
qed

lemma \<T>\<^sub>G_complete:
  "funas_gterm s \<subseteq> \<F> \<Longrightarrow> s \<in> \<T>\<^sub>G \<F> "
  by (induct s) (auto simp: SUP_le_iff)

lemma \<T>\<^sub>G_funas_gterm_conv:
  "s \<in> \<T>\<^sub>G \<F> \<longleftrightarrow> funas_gterm s \<subseteq> \<F>"
  using \<T>\<^sub>G_sound \<T>\<^sub>G_complete by auto

lemma \<T>\<^sub>G_equivalent_def:
  "\<T>\<^sub>G \<F> = gterms \<F>"
  using \<T>\<^sub>G_funas_gterm_conv by auto

lemma \<T>\<^sub>G_intersection [simp]:
  "s \<in> \<T>\<^sub>G \<F> \<Longrightarrow> s \<in> \<T>\<^sub>G \<G> \<Longrightarrow> s \<in> \<T>\<^sub>G (\<F> \<inter> \<G>)"
  by (auto simp: \<T>\<^sub>G_funas_gterm_conv \<T>\<^sub>G_equivalent_def)

lemma \<T>\<^sub>G_mono:
  "\<G> \<subseteq> \<F> \<Longrightarrow> \<T>\<^sub>G \<G> \<subseteq> \<T>\<^sub>G \<F>"
  using gterms_mono by (simp add: \<T>\<^sub>G_equivalent_def)

lemma \<T>\<^sub>G_UNIV [simp]: "s \<in> \<T>\<^sub>G UNIV"
  by (induct) auto

definition funas_grel where
  "funas_grel \<R> = \<Union> ((\<lambda> (s, t). funas_gterm s \<union> funas_gterm t) ` \<R>)"

end