section \<open>Pattern Completeness\<close>

text \<open>Pattern-completeness is the question whether in a given program all terms
  of the form f(c1,..,cn) are matched by some lhs of the program,
  where here each ci is a constructor ground term and f is a defined symbol.
  This will be represented as a pattern problem of the shape 
  (f(x1,...xn), {lhs1, ..., lhsn}) where the xi will represent arbitrary constructor terms.\<close>

section \<open>A Set-Based Inference System to Decide Pattern Completeness\<close>

text \<open>This theory contains an algorithm to decide whether pattern problems are complete.
  It represents the inference rules of the paper on the set-based level.

  On this level we prove partial correctness and preservation of well-formed inputs,
  but not termination.\<close>

theory Pattern_Completeness_Set
  imports
    First_Order_Terms.Term_More
    Complete_Non_Orders.Complete_Relations
    Sorted_Terms.Sorted_Contexts
    Compute_Nonempty_Infinite_Sorts
begin

lemmas type_conversion = hastype_in_Term_empty_imp_subst

lemma ball_insert_un_cong: "f y = Ball zs f \<Longrightarrow> Ball (insert y A) f = Ball (zs \<union> A) f"
  by auto

lemma bex_insert_cong: "f y = f z \<Longrightarrow> Bex (insert y A) f = Bex (insert z A) f"
  by auto

lemma not_bdd_above_natD: 
  assumes "\<not> bdd_above (A :: nat set)"
  shows "\<exists> x \<in> A. x > n" 
  using assms by (meson bdd_above.unfold linorder_le_cases order.strict_iff)

lemma list_eq_nth_eq: "xs = ys \<longleftrightarrow> length xs = length ys \<and> (\<forall> i < length ys. xs ! i = ys ! i)"
  using nth_equalityI by metis

lemma subt_size: "p \<in> poss t \<Longrightarrow> size (t |_ p) \<le> size t"
proof (induct p arbitrary: t)
  case (Cons i p t)
  thus ?case 
  proof (cases t)
    case (Fun f ss)
    from Cons Fun have i: "i < length ss" and sub: "t |_ (i # p) = (ss ! i) |_ p" 
      and "p \<in> poss (ss ! i)" by auto
    with Cons(1)[OF this(3)]
    have "size (t |_ (i # p)) \<le> size (ss ! i)" by auto
    also have "\<dots> \<le> size t" using i unfolding Fun by (simp add: termination_simp)
    finally show ?thesis .
  qed auto
qed auto

lemma removeAll_remdups: "removeAll x (remdups ys) = remdups (removeAll x ys)"
  by (simp add: remdups_filter removeAll_filter_not_eq)

lemma removeAll_eq_Nil_iff: "removeAll x ys = [] \<longleftrightarrow> (\<forall>y \<in> set ys. y = x)"
  by (induction ys, auto)

lemma concat_removeAll_Nil: "concat (removeAll [] xss) = concat xss"
  by (induction xss, auto)

lemma removeAll_eq_imp_concat_eq:
  assumes "removeAll [] xss = removeAll [] xss'"
  shows "concat xss = concat xss'"
  apply (subst (1 2) concat_removeAll_Nil[symmetric])
  by (simp add: assms)

lemma map_remdups_commute:
  assumes "inj_on f (set xs)"
  shows "map f (remdups xs) = remdups (map f xs)"
  using assms by (induction xs, auto)

lemma Uniq_False: "\<exists>\<^sub>\<le>\<^sub>1 a. False" by (auto intro!: Uniq_I)

abbreviation "UNIQ A \<equiv> \<exists>\<^sub>\<le>\<^sub>1 a. a \<in> A"

lemma Uniq_eq_the_elem:
  assumes "UNIQ A" and "a \<in> A" shows "a = the_elem A"
  using the1_equality'[OF assms]
  by (metis assms empty_iff is_singletonI' is_singleton_some_elem
      some_elem_nonempty the1_equality' the_elem_eq)

lemma bij_betw_imp_Uniq_iff:
  assumes "bij_betw f A B" shows "UNIQ A \<longleftrightarrow> UNIQ B"
  using assms[THEN bij_betw_imp_surj_on]
  apply (auto simp: Uniq_def)
  by (metis assms bij_betw_def imageI inv_into_f_eq)

lemma image_Uniq: "UNIQ A \<Longrightarrow> UNIQ (f ` A)"
  by (smt (verit) Uniq_I image_iff the1_equality')

lemma successively_eq_iff_Uniq: "successively (=) xs \<longleftrightarrow> UNIQ (set xs)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (induction xs rule: induct_list012)
    by (auto intro: Uniq_I)
  show "?r \<Longrightarrow> ?l"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case xxs: (Cons x xs)
    show ?case
    proof (cases xs)
      case Nil
      then show ?thesis by simp
    next
      case xs: (Cons y ys)
      have "successively (=) xs"
        apply (rule xxs(1)) using xxs(2) by (simp add: Uniq_def)
      with xxs(2)
      show ?thesis by (auto simp: xs Uniq_def)
    qed
  qed
qed

subsection \<open>Defining Pattern Completeness\<close>

text \<open>
  We first consider matching problems, which are set of matching atoms.
  Each matching atom is a pair of terms: matchee and pattern.
  Matchee and pattern may have different type of variables: 
  Matchees use natural numbers (annotated with sorts) as variables, 
  so that it is easy to generate new variables,
  whereas patterns allow arbitrary variables of type \<open>'v\<close> without any further information.
  Then pattern problems are sets of matching problems, and we also have sets of pattern problems.

  The suffix \<open>_set\<close> is used to indicate that here these problems are modeled via sets.\<close>

abbreviation tvars :: "nat \<times> 's \<rightharpoonup> 's" ("\<V>") where "\<V> \<equiv> sort_annotated"

type_synonym ('f,'v,'s)match_atom = "('f,nat \<times> 's)term \<times> ('f,'v)term"
type_synonym ('f,'v,'s)match_problem_set = "('f,'v,'s) match_atom set" 
type_synonym ('f,'v,'s)pat_problem_set = "('f,'v,'s)match_problem_set set" 
type_synonym ('f,'v,'s)pats_problem_set = "('f,'v,'s)pat_problem_set set" 

abbreviation (input) bottom :: "('f,'v,'s)pats_problem_set" where "bottom \<equiv> {{}}"

definition tvars_match :: "('f,'v,'s)match_problem_set \<Rightarrow> (nat \<times> 's) set" where
  "tvars_match mp = (\<Union>(t,l) \<in> mp. vars t)"

definition tvars_pat :: "('f,'v,'s)pat_problem_set \<Rightarrow> (nat \<times> 's) set" where
  "tvars_pat pp = (\<Union>mp \<in> pp. tvars_match mp)"

definition tvars_pats :: "('f,'v,'s)pats_problem_set \<Rightarrow> (nat \<times> 's) set" where
  "tvars_pats P = (\<Union>pp \<in> P. tvars_pat pp)"

definition subst_left :: "('f,nat \<times> 's)subst \<Rightarrow> (('f,nat \<times> 's)term \<times> ('f,'v)term) \<Rightarrow> (('f,nat \<times> 's)term \<times> ('f,'v)term)" where
  "subst_left \<tau> = (\<lambda>(t,r). (t \<cdot> \<tau>, r))"

text \<open>A definition of pattern completeness for pattern problems.\<close>

definition match_complete_wrt :: "('f,nat \<times> 's,'w)gsubst \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "match_complete_wrt \<sigma> mp = (\<exists> \<mu>. \<forall> (t,l) \<in> mp. t \<cdot> \<sigma> = l \<cdot> \<mu>)" 

lemma match_complete_wrt_cong:
  assumes s: "\<And>x. x \<in> tvars_match mp \<Longrightarrow> \<sigma> x = \<sigma>' x"
    and mp: "mp = mp'"
  shows "match_complete_wrt \<sigma> mp = match_complete_wrt \<sigma>' mp'"
  apply (unfold match_complete_wrt_def Ball_Pair_conv mp[symmetric])
  apply (intro ex_cong1 all_cong1 imp_cong[OF refl])
proof-
  fix \<mu> t l assume "(t,l) \<in> mp"
  with s have "\<forall>x \<in> vars t. \<sigma> x = \<sigma>' x" by (auto simp: tvars_match_def)
  from subst_same_vars[OF this] show "t\<cdot>\<sigma> = l\<cdot>\<mu> \<longleftrightarrow> t\<cdot>\<sigma>' = l\<cdot>\<mu>" by simp
qed

lemma match_complete_wrt_imp_o:
  assumes "match_complete_wrt \<sigma> mp" shows "match_complete_wrt (\<sigma> \<circ>\<^sub>s \<tau>) mp"
proof (unfold match_complete_wrt_def)
  from assms[unfolded match_complete_wrt_def] obtain \<mu> where eq: "\<forall>(t,l) \<in> mp. t\<cdot>\<sigma> = l\<cdot>\<mu>"
    by auto
  { fix t l
    assume tl: "(t,l) \<in> mp"
    with eq have "t\<cdot>(\<sigma> \<circ>\<^sub>s \<tau>) = l\<cdot>(\<mu> \<circ>\<^sub>s \<tau>)" by auto
  }
  then show "\<exists>\<mu>'. \<forall>(t,l) \<in> mp. t\<cdot>(\<sigma> \<circ>\<^sub>s \<tau>) = l\<cdot>\<mu>'" by blast
qed

lemma match_complete_wrt_o_imp:
  assumes s: "\<sigma> :\<^sub>s \<V> |` tvars_match mp \<rightarrow> \<T>(C,\<emptyset>)" and m: "match_complete_wrt (\<sigma> \<circ>\<^sub>s \<tau>) mp"
  shows "match_complete_wrt \<sigma> mp"
proof (unfold match_complete_wrt_def)
  from m[unfolded match_complete_wrt_def] obtain \<mu> where eq: "\<forall>(t,l) \<in> mp. t\<cdot>\<sigma>\<cdot>\<tau> = l\<cdot>\<mu>"
    by auto
  have "\<forall>x \<in> tvars_match mp. \<sigma> x : snd x in \<T>(C,\<emptyset>)"
    by (auto intro!: sorted_mapD[OF s] simp: hastype_restrict)
  then have g: "x \<in> tvars_match mp \<Longrightarrow> ground (\<sigma> x)" for x
    by (auto simp: hatype_imp_ground)
  { fix t l
    assume tl: "(t,l) \<in> mp"
    then have "ground (t\<cdot>\<sigma>)" by (force intro!: g simp: tvars_match_def)
    then have "t\<cdot>\<sigma>\<cdot>\<tau>\<cdot>undefined = t\<cdot>\<sigma>" by (metis eval_subst ground_subst_apply)
    with tl eq have "t\<cdot>\<sigma> = l\<cdot>(\<mu> \<circ>\<^sub>s undefined)" by auto
  }
  then show "\<exists>\<mu>'. \<forall>(t,l) \<in> mp. t\<cdot>\<sigma> = l\<cdot>\<mu>'" by blast
qed

text \<open>Pattern completeness is match completeness w.r.t. any constructor-ground substitution.
  Note that variables to instantiate are represented as pairs of (number, sort).\<close>

definition pat_complete :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "pat_complete C pp \<longleftrightarrow> (\<forall>\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C). \<exists> mp \<in> pp. match_complete_wrt \<sigma> mp)"

lemma pat_completeD:
  assumes pp: "pat_complete C pp"
    and s: "\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C,\<emptyset>)"
  shows "\<exists> mp \<in> pp. match_complete_wrt \<sigma> mp"
proof -
  from s have "\<sigma> \<circ>\<^sub>s undefined :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C)"
    by (simp add: subst_compose_sorted_map)
  from pp[unfolded pat_complete_def, rule_format, OF this]
  obtain mp where mp: "mp \<in> pp"
    and m: "match_complete_wrt (\<sigma> \<circ>\<^sub>s undefined :: _ \<Rightarrow> (_,unit) term) mp" 
    by auto
  have "\<sigma> :\<^sub>s \<V> |` tvars_match mp \<rightarrow> \<T>(C,\<emptyset>)"
    apply (rule sorted_map_cmono[OF s])
    using mp
    by (auto simp: tvars_pat_def intro!: restrict_map_mono_right)
  from match_complete_wrt_o_imp[OF this m] mp
  show ?thesis by auto
qed

lemma pat_completeI:
  assumes r: "\<forall>\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C,\<emptyset>::'v\<rightharpoonup>'s). \<exists> mp \<in> pp. match_complete_wrt \<sigma> mp"
  shows "pat_complete C pp"
proof (unfold pat_complete_def, safe)
  fix \<sigma> assume s: "\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C)"
  then have "\<sigma> \<circ>\<^sub>s undefined :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C,\<emptyset>)"
    by (simp add: subst_compose_sorted_map)
  from r[rule_format, OF this]
  obtain mp where mp: "mp \<in> pp" and m: "match_complete_wrt (\<sigma> \<circ>\<^sub>s undefined::_\<Rightarrow>(_,'v) term) mp" 
    by auto
  have "\<sigma> :\<^sub>s \<V> |` tvars_match mp \<rightarrow> \<T>(C)"
    apply (rule sorted_map_cmono[OF s restrict_map_mono_right])
    using mp by (auto simp: tvars_pat_def)
  from match_complete_wrt_o_imp[OF this m] mp
  show "Bex pp (match_complete_wrt \<sigma>)" by auto
qed

lemma tvars_pat_empty[simp]: "tvars_pat {} = {}"
  by (simp add: tvars_pat_def)

lemma pat_complete_empty[simp]: "pat_complete C {} = False" 
  unfolding pat_complete_def by simp

abbreviation pats_complete :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)pats_problem_set \<Rightarrow> bool" where
  "pats_complete C P \<equiv> \<forall>pp \<in> P. pat_complete C pp"
(*  "pats_complete C P \<equiv> \<forall>\<sigma> :\<^sub>s \<V> |` tvars_pats P \<rightarrow> \<T>(C). \<forall>pp \<in> P. \<exists> mp \<in> pp. match_complete_wrt \<sigma> mp"
*)

subsection \<open>Definition of Algorithm -- Inference Rules\<close>

text \<open>A function to compute for a variable $x$ all substitution that instantiate
  $x$ by $c(x_n, ..., x_{n+a})$ where $c$ is a constructor of arity $a$ and $n$ is a parameter that
  determines from where to start the numbering of variables.\<close>

definition \<tau>c :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> 'f \<times> 's list \<Rightarrow> ('f,nat \<times> 's)subst" where 
  "\<tau>c n x = (\<lambda>(f,ss). subst x (Fun f (map Var (zip [n ..< n + length ss] ss))))"

text \<open>Compute the list of conflicting variables (Some list), or detect a clash (None)\<close>
fun conflicts :: "('f,'v\<times>'s)term \<Rightarrow> ('f,'v\<times>'s)term \<Rightarrow> ('v\<times>'s) list option" where 
  "conflicts (Var x) (Var y) = (if x = y then Some [] else
   if snd x = snd y then Some [x,y] else None)"
| "conflicts (Var x) (Fun _ _) = (Some [x])"
| "conflicts (Fun _ _) (Var x) = (Some [x])" 
| "conflicts (Fun f ss) (Fun g ts) = (if (f,length ss) = (g,length ts)
     then map_option concat (those (map2 conflicts ss ts))
    else None)" 

abbreviation "Conflict_Var s t x \<equiv> conflicts s t \<noteq> None \<and> x \<in> set (the (conflicts s t))" 
abbreviation "Conflict_Clash s t \<equiv> conflicts s t = None" 

lemma conflicts_sym: "rel_option (\<lambda> xs ys. set xs = set ys) (conflicts s t) (conflicts t s)" (is "rel_option _ (?c s t) _")
proof (induct s t rule: conflicts.induct)
  case (4 f ss g ts)
  define c where "c = ?c" 
  show ?case
  proof (cases "(f,length ss) = (g,length ts)")
    case True
    hence len: "length ss = length ts" 
      "((f, length ss) = (g, length ts)) = True"
      "((g, length ts) = (f, length ss)) = True" by auto
    show ?thesis using len(1) 4[OF True _ refl]
      unfolding conflicts.simps len(2,3) if_True
      unfolding option.rel_map c_def[symmetric] set_concat
    proof (induct ss ts rule: list_induct2, goal_cases)
      case (2 s ss t ts)
      hence IH: "rel_option (\<lambda>x y. \<Union> (set ` set x) = \<Union> (set ` set y)) (those (map2 c ss ts)) (those (map2 c ts ss))" by auto
      from 2 have st: "rel_option (\<lambda>xs ys. set xs = set ys) (c s t) (c t s)" by auto
      from IH st show ?case by (cases "c s t"; cases "c t s"; auto simp: option.rel_map)
        (simp add: option.rel_sel)
    qed simp
  qed auto
qed auto


lemma conflicts:
  shows "Conflict_Clash s t \<Longrightarrow>
    \<exists> p. p \<in> poss s \<and> p \<in> poss t \<and>
    (is_Fun (s |_p) \<and> is_Fun (t |_p) \<and> root (s |_p) \<noteq> root (t |_ p) \<or>
    (\<exists>x y. s |_p = Var x \<and> t |_p = Var y \<and> snd x \<noteq> snd y))"
    (is "?B1 \<Longrightarrow> ?B2")
    and "Conflict_Var s t x \<Longrightarrow>
    \<exists> p . p \<in> poss s \<and> p \<in> poss t \<and> s |_p \<noteq> t |_p \<and>
    (s |_p = Var x \<or> t |_p = Var x)"
    (is "?C1 x \<Longrightarrow> ?C2 x")
    and "s \<noteq> t \<Longrightarrow> \<exists> x. Conflict_Clash s t \<or> Conflict_Var s t x" 
    and "Conflict_Var s t x \<Longrightarrow> x \<in> vars s \<union> vars t" 
    and "conflicts s t = Some [] \<longleftrightarrow> s = t" (is ?A)
proof -
  let ?B = "?B1 \<longrightarrow> ?B2" 
  let ?C = "\<lambda> x. ?C1 x \<longrightarrow> ?C2 x" 
  {
    fix x
    have "(conflicts s t = Some [] \<longrightarrow> s = t) \<and> ?B \<and> ?C x"
    proof (induction s arbitrary: t)
      case (Var y t)
      thus ?case by (cases t, cases y, auto)
    next
      case (Fun f ss t)
      show ?case 
      proof (cases t)
        case t: (Fun g ts)
        show ?thesis
        proof (cases "(f,length ss) = (g,length ts)")
          case False
          hence res: "conflicts (Fun f ss) t = None" unfolding t by auto
          show ?thesis unfolding res unfolding t using False
            by (auto intro!: exI[of _ Nil])
        next
          case f: True
          let ?s = "Fun f ss" 
          show ?thesis 
          proof (cases "those (map2 conflicts ss ts)")
            case None
            hence res: "conflicts ?s t = None" unfolding t by auto
            from None[unfolded those_eq_None] obtain i where i: "i < length ss" "i < length ts" and 
              confl: "conflicts (ss ! i) (ts ! i) = None"
              using f unfolding set_conv_nth set_zip by auto
            from i have "ss ! i \<in> set ss" by auto
            from Fun.IH[OF this, of "ts ! i"] confl obtain p 
              where p: "p \<in> poss (ss ! i) \<and> p \<in> poss (ts ! i) \<and>
(is_Fun (ss ! i |_ p) \<and> is_Fun (ts ! i |_ p) \<and> root (ss ! i |_ p) \<noteq> root (ts ! i |_ p) \<or>
(\<exists>x y. ss!i |_ p = Var x \<and> ts!i |_ p = Var y \<and> snd x \<noteq> snd y))" 
              by force
            from p have p: "\<exists> p. p \<in> poss ?s \<and> p \<in> poss t \<and>
(is_Fun (?s |_ p) \<and> is_Fun (t |_ p) \<and> root (?s |_ p) \<noteq> root (t |_ p) \<or>
(\<exists>x y. ?s |_ p = Var x \<and> t |_ p = Var y \<and> snd x \<noteq> snd y))" 
              by (intro exI[of _ "i # p"], unfold t, insert i f, auto)
            from p res show ?thesis by auto
          next
            case (Some xss)
            hence res: "conflicts ?s t = Some (concat xss)" unfolding t using f by auto
            from Some have map2: "map2 conflicts ss ts = map Some xss" by auto
            from arg_cong[OF this, of length] have len: "length xss = length ss" using f by auto
            have rec: "i < length ss \<Longrightarrow> conflicts (ss ! i) (ts ! i) = Some (xss ! i)" for i 
              using arg_cong[OF map2, of "\<lambda> xs. xs ! i"] len f by auto
            {
              assume "x \<in> set (the (conflicts ?s t))" 
              hence "x \<in> set (concat xss)" unfolding res by auto
              then obtain xs where xs: "xs \<in> set xss" and x: "x \<in> set xs" by auto
              from xs len obtain i where i: "i < length ss" and xs: "xs = xss ! i" by (auto simp: set_conv_nth)
              from i have "ss ! i \<in> set ss" by auto
              from Fun.IH[OF this, of "ts ! i", unfolded rec[OF i, folded xs]] x
              obtain p where "p \<in> poss (ss ! i) \<and> p \<in> poss (ts ! i) \<and> ss ! i |_ p \<noteq> ts ! i |_ p \<and> (ss ! i |_ p = Var x \<or> ts ! i |_ p = Var x)" 
                by auto
              hence "\<exists> p. p \<in> poss ?s \<and> p \<in> poss t \<and> ?s |_ p \<noteq> t |_ p \<and> (?s |_ p = Var x \<or> t |_ p = Var x)" 
                by (intro exI[of _ "i # p"], insert i f, auto simp: t)
            }
            moreover
            {
              assume "conflicts ?s t = Some []" 
              with res have empty: "concat xss = []" by auto
              {
                fix i
                assume i: "i < length ss" 
                from rec[OF i] have "conflicts (ss ! i) (ts ! i) = Some (xss ! i)" .
                moreover from empty i len have "xss ! i = []" by auto
                ultimately have res: "conflicts (ss ! i) (ts ! i) = Some []" by simp
                from i have "ss ! i \<in> set ss" by auto
                from Fun.IH[OF this, of "ts ! i", unfolded res] have "ss ! i = ts ! i" by auto
              }
              with f have "?s = t" unfolding t by (auto intro: nth_equalityI)
            }
            ultimately show ?thesis unfolding res by auto
          qed
        qed
      qed auto
    qed
  } note main = this
  from main show B: "?B1 \<Longrightarrow> ?B2" and C: "?C1 x \<Longrightarrow> ?C2 x" by blast+
  show ?A
  proof
    assume "s = t" 
    with B have "conflicts s t \<noteq> None" by force
    then obtain xs where res: "conflicts s t = Some xs" by auto     
    show "conflicts s t = Some []" 
    proof (cases xs)
      case Nil 
      thus ?thesis using res by auto
    next
      case (Cons x xs)
      with main[of x] res \<open>s = t\<close> show ?thesis by auto
    qed
  qed (insert main, blast)
  {
    assume diff: "s \<noteq> t" 
    show "\<exists> x. Conflict_Clash s t \<or> Conflict_Var s t x" 
    proof (cases "conflicts s t")
      case (Some xs)
      with \<open>?A\<close> diff obtain x where "x \<in> set xs" by (cases xs, auto)
      thus ?thesis unfolding Some
        apply auto
        by (metis surj_pair)
    qed auto
  }
  assume "Conflict_Var s t x" 
  with C obtain p where "p \<in> poss s" "p \<in> poss t" "(s |_ p = Var x \<or> t |_ p = Var x)" 
    by blast
  thus "x \<in> vars s \<union> vars t" 
    by (metis UnCI subt_at_imp_supteq' subteq_Var_imp_in_vars_term)
qed

declare conflicts.simps[simp del] 

lemma conflicts_refl[simp]: "conflicts t t = Some []" 
  using conflicts(5)[of t t] by auto

locale pattern_completeness_context =
  fixes S :: "'s set" \<comment> \<open>set of sort-names\<close>
    and C :: "('f,'s)ssig" \<comment> \<open>sorted signature\<close>
    and m :: nat \<comment> \<open>upper bound on arities of constructors\<close>
    and Cl :: "'s \<Rightarrow> ('f \<times> 's list)list" \<comment> \<open>a function to compute all constructors of given sort as list\<close> 
    and inf_sort :: "'s \<Rightarrow> bool" \<comment> \<open>a function to indicate whether a sort is infinite\<close>
    and cd_sort :: "'s \<Rightarrow> nat" \<comment> \<open>a function to compute finite cardinality of a sort\<close>
    and improved :: bool \<comment> \<open>if improved = False, then FSCD-version of algorithm is used;
                             if improved = True, the better journal version (under development) is used.\<close>
begin

definition tvars_disj_pp :: "nat set \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "tvars_disj_pp V p = (\<forall> mp \<in> p. \<forall> (ti,pi) \<in> mp. fst ` vars ti \<inter> V = {})" 

definition lvars_disj_mp :: "'v list \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "lvars_disj_mp ys mp = (\<Union> (vars ` snd ` mp) \<inter> set ys = {} \<and> distinct ys)" 

definition inf_var_conflict :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "inf_var_conflict mp = (\<exists> s t x y. 
    (s,Var x) \<in> mp \<and> (t,Var x) \<in> mp \<and> Conflict_Var s t y \<and> inf_sort (snd y))" 

definition subst_match_problem_set :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> ('f,'v,'s)match_problem_set" where
  "subst_match_problem_set \<tau> mp = subst_left \<tau> ` mp" 

definition subst_pat_problem_set :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> ('f,'v,'s)pat_problem_set" where
  "subst_pat_problem_set \<tau> pp = subst_match_problem_set \<tau> ` pp"

definition \<tau>s :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> ('f,nat \<times> 's)subst set" where 
  "\<tau>s n x = {\<tau>c n x (f,ss) | f ss. f : ss \<rightarrow> snd x in C}" 

text \<open>The transformation rules of the paper.

The formal definition contains two deviations from the rules in the paper: first, the instantiate-rule
can always be applied; and second there is an identity rule, which will simplify later refinement 
proofs. Both of the deviations cause non-termination.

The formal inference rules further separate those rules that deliver a bottom- or top-element from
the ones that deliver a transformed problem.\<close>
inductive mp_step :: "('f,'v,'s)match_problem_set \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool"
(infix \<open>\<rightarrow>\<^sub>s\<close> 50) where
  mp_decompose: "length ts = length ls \<Longrightarrow> insert (Fun f ts, Fun f ls) mp \<rightarrow>\<^sub>s set (zip ts ls) \<union> mp"
| mp_match: "x \<notin> \<Union> (vars ` snd ` mp) \<Longrightarrow> insert (t, Var x) mp \<rightarrow>\<^sub>s mp" 
| mp_identity: "mp \<rightarrow>\<^sub>s mp"
| mp_decompose': "mp \<union> mp' \<rightarrow>\<^sub>s (\<Union> (t, l) \<in> mp. set (zip (args t) (map Var ys))) \<union> mp'" 
if "\<And> t l. (t,l) \<in> mp \<Longrightarrow> l = Var y \<and> root t = Some (f,n)" 
   "\<And> t l. (t,l) \<in> mp' \<Longrightarrow> y \<notin> vars l"
   "lvars_disj_mp ys (mp \<union> mp')" "length ys = n" (* ys = n fresh vars *) 
   improved (* decompose' is not available in FSCD version *)

inductive mp_fail :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  mp_clash: "(f,length ts) \<noteq> (g,length ls) \<Longrightarrow> mp_fail (insert (Fun f ts, Fun g ls) mp)" 
| mp_clash': "Conflict_Clash s t \<Longrightarrow> mp_fail ({(s,Var x),(t, Var x)} \<union> mp)"

inductive pp_step :: "('f,'v,'s)pat_problem_set \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool"
(infix \<open>\<Rightarrow>\<^sub>s\<close> 50) where
  pp_simp_mp: "mp \<rightarrow>\<^sub>s mp' \<Longrightarrow> insert mp pp \<Rightarrow>\<^sub>s insert mp' pp" 
| pp_remove_mp: "mp_fail mp \<Longrightarrow> insert mp pp \<Rightarrow>\<^sub>s pp"
| pp_inf_var_conflict: "pp \<union> pp' \<Rightarrow>\<^sub>s pp'" 
  if "Ball pp inf_var_conflict" 
    "finite pp" 
    "Ball (tvars_pat pp') (\<lambda> x. \<not> inf_sort (snd x))" 
    "\<not> improved \<Longrightarrow> pp' = {}" (* no pp' allowed in FSCD algorithm *)

text \<open>Note that in @{thm[source] pp_inf_var_conflict} the conflicts have to be simultaneously occurring. 
  If just some matching problem has such a conflict, then this cannot be deleted immediately!

  Example-program: f(x,x) = ..., f(s(x),y) = ..., f(x,s(y)) = ... cover all cases of natural numbers,
    i.e., f(x1,x2), but if one would immediately delete the matching problem of the first lhs
    because of the resulting @{const inf_var_conflict} in {(x1,x),(x2,x)} then it is no longer complete.\<close>


inductive pp_success :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "pp_success (insert {} pp)" 

inductive P_step_set :: "('f,'v,'s)pats_problem_set \<Rightarrow> ('f,'v,'s)pats_problem_set \<Rightarrow> bool"
(infix \<open>\<Rrightarrow>\<^sub>s\<close> 50) where
  P_fail: "insert {} P \<Rrightarrow>\<^sub>s bottom"
| P_simp: "pp \<Rightarrow>\<^sub>s pp' \<Longrightarrow> insert pp P \<Rrightarrow>\<^sub>s insert pp' P"
| P_remove_pp: "pp_success pp \<Longrightarrow> insert pp P \<Rrightarrow>\<^sub>s P"
| P_instantiate: "tvars_disj_pp {n ..< n+m} pp \<Longrightarrow> x \<in> tvars_pat pp \<Longrightarrow>
    insert pp P \<Rrightarrow>\<^sub>s {subst_pat_problem_set \<tau> pp |. \<tau> \<in> \<tau>s n x} \<union> P"


subsection \<open>Soundness of the inference rules\<close>

text \<open>Well-formed matching and pattern problems: all occurring variables 
  (in left-hand sides of matching problems) have a known sort.\<close>
definition wf_match :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "wf_match mp = (snd ` tvars_match mp \<subseteq> S)" 

lemma wf_match_iff: "wf_match mp \<longleftrightarrow> (\<forall>(x,\<iota>) \<in> tvars_match mp. \<iota> \<in> S)"
  by (auto simp: wf_match_def)

lemma tvars_match_subst: "tvars_match (subst_match_problem_set \<sigma> mp) = (\<Union>(t,l) \<in> mp. vars (t\<cdot>\<sigma>))"
  by (auto simp: tvars_match_def subst_match_problem_set_def subst_left_def)

lemma wf_match_subst:
  assumes s: "\<sigma> :\<^sub>s \<V> |` tvars_match mp \<rightarrow> \<T>(C',{x : \<iota> in \<V>. \<iota> \<in> S})"
  shows "wf_match (subst_match_problem_set \<sigma> mp)"
  apply (unfold wf_match_iff tvars_match_subst)
proof (safe)
  fix t l x \<iota> assume tl: "(t,l) \<in> mp" and xt: "(x,\<iota>) \<in> vars (t\<cdot>\<sigma>)"
  from xt obtain y \<kappa> where y: "(y,\<kappa>) \<in> vars t" and xy: "(x,\<iota>) \<in> vars (\<sigma> (y,\<kappa>))" by (auto simp: vars_term_subst)
  from tl y have "(y,\<kappa>) : \<kappa> in \<V> |` tvars_match mp" by (auto simp: hastype_restrict tvars_match_def)
  from sorted_mapD[OF s this]
  have "\<sigma> (y,\<kappa>) : \<kappa> in \<T>(C',{x : \<iota> in \<V>. \<iota> \<in> S})".
  from hastype_in_Term_imp_vars[OF this xy]
  have "(x,\<iota>) : \<iota> in {x : \<iota> in \<V>. \<iota> \<in> S}" by (auto elim!: in_dom_hastypeE)
  then show "\<iota> \<in> S" by auto
qed

definition wf_pat :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "wf_pat pp = (\<forall>mp \<in> pp. wf_match mp)"

lemma wf_pat_subst:
  assumes s: "\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C',{x : \<iota> in \<V>. \<iota> \<in> S})"
  shows "wf_pat (subst_pat_problem_set \<sigma> pp)"
  apply (unfold wf_pat_def subst_pat_problem_set_def)
proof safe
  fix mp assume mp: "mp \<in> pp"
  show "wf_match (subst_match_problem_set \<sigma> mp)"
    apply (rule wf_match_subst)
    apply (rule sorted_map_cmono[OF s])
    apply (rule restrict_map_mono_right) using mp by (auto simp: tvars_pat_def)
qed

definition wf_pats :: "('f,'v,'s)pats_problem_set \<Rightarrow> bool" where
  "wf_pats P = (\<forall>pp \<in> P. wf_pat pp)"

lemma wf_pat_iff: "wf_pat pp \<longleftrightarrow> (\<forall>(x,\<iota>) \<in> tvars_pat pp. \<iota> \<in> S)"
  by (auto simp: wf_pat_def tvars_pat_def wf_match_iff)

text \<open>The reduction of match problems preserves completeness.\<close>

lemma mp_step_pcorrect: "mp \<rightarrow>\<^sub>s mp' \<Longrightarrow> match_complete_wrt \<sigma> mp = match_complete_wrt \<sigma> mp'" 
proof (induct mp mp' rule: mp_step.induct)
  case *: (mp_decompose f ts ls mp)
  show ?case unfolding match_complete_wrt_def
    apply (rule ex_cong1)
    apply (rule ball_insert_un_cong)
    apply (unfold split) using * by (auto simp add: set_zip list_eq_nth_eq)
next
  case *: (mp_match x mp t)
  show ?case unfolding match_complete_wrt_def
  proof 
    assume "\<exists>\<mu>. \<forall>(ti, li)\<in>mp. ti \<cdot> \<sigma> = li \<cdot> \<mu>" 
    then obtain \<mu> where eq: "\<And> ti li. (ti, li)\<in>mp \<Longrightarrow>  ti \<cdot> \<sigma> = li \<cdot> \<mu>" by auto
    let ?\<mu> = "\<mu>(x := t \<cdot> \<sigma>)" 
    have "(ti, li) \<in> mp \<Longrightarrow> ti \<cdot> \<sigma> = li \<cdot> ?\<mu>" for ti li using * eq[of ti li]
      by (auto intro!: term_subst_eq)
    thus "\<exists>\<mu>. \<forall>(ti, li)\<in>insert (t, Var x) mp. ti \<cdot> \<sigma> = li \<cdot> \<mu>" by (intro exI[of _ ?\<mu>], auto)
  qed auto
next
  case *: (mp_decompose' mp y f n mp' ys)
  note * = *[unfolded lvars_disj_mp_def]
  let ?mpi = "(\<Union>(t, l)\<in>mp. set (zip (args t) (map Var ys)))" 
  let ?y = "Var y" 
  show ?case
  proof
    assume "match_complete_wrt \<sigma> (?mpi \<union> mp')" 
    from this[unfolded match_complete_wrt_def] obtain \<mu>
      where match: "\<And> t l. (t,l) \<in> ?mpi \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>" 
        and match': "\<And> t l. (t,l) \<in> mp' \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>" by force
    let ?\<mu> = "\<mu>( y := Fun f (map \<mu> ys))" 
    show "match_complete_wrt \<sigma> (mp \<union> mp')" unfolding match_complete_wrt_def
    proof (intro exI[of _ ?\<mu>] ballI, elim UnE; clarify)
      fix t l
      {
        assume "(t,l) \<in> mp'" 
        from match'[OF this] *(2)[OF this]
        show "t \<cdot> \<sigma> = l \<cdot> ?\<mu>" by (auto intro: term_subst_eq)
      }
      assume tl: "(t,l) \<in> mp"
      from *(1)[OF this] obtain ts where l: "l = Var y" and t: "t = Fun f ts"  
        and lts: "length ts = n" by (cases t, auto)
      {
        fix ti yi
        assume "(ti,yi) \<in> set (zip ts ys)" 
        hence "(ti, Var yi) \<in> set (zip (args t) (map Var ys))" 
          using t lts \<open>length ys = n\<close> by (force simp: set_conv_nth)
        hence "(ti, Var yi) \<in> ?mpi" using tl by blast
        from match[OF this] have "\<mu> yi = ti \<cdot> \<sigma>" by simp
      } note yi = this
      show "t \<cdot> \<sigma> = l \<cdot> ?\<mu>" unfolding l t using yi lts \<open>length ys = n\<close> 
        by (force intro!: nth_equalityI simp: set_zip)
    qed
  next
    assume "match_complete_wrt \<sigma> (mp \<union> mp')" 
    from this[unfolded match_complete_wrt_def]
    obtain \<mu> where match: "\<And> t l. (t,l) \<in> mp \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>"
      and match': "\<And> t l. (t,l) \<in> mp' \<Longrightarrow> t \<cdot> \<sigma> = l \<cdot> \<mu>" by force
    define \<mu>' where "\<mu>' = (\<lambda> x. case map_of (zip ys (args (\<mu> y))) x of 
      None \<Rightarrow> \<mu> x | Some Ti \<Rightarrow> Ti)"
    show "match_complete_wrt \<sigma> (?mpi \<union> mp')" 
      unfolding match_complete_wrt_def
    proof (intro exI[of _ \<mu>'] ballI, elim UnE; clarify)
      fix t l
      assume tl: "(t,l) \<in> mp'" 
      from *(3) tl have vars: "vars l \<inter> set ys = {}" by force
      hence "map_of (zip ys (args (\<mu> y))) x = None" if "x \<in> vars l" for x
        using that by (meson disjoint_iff map_of_SomeD option.exhaust set_zip_leftD)
      with match'[OF tl] 
      show "t \<cdot> \<sigma> = l \<cdot> \<mu>'" by (auto intro!: term_subst_eq simp: \<mu>'_def)
    next
      fix t l ti and vyi :: "('f,_)term" 
      assume tl: "(t,l) \<in> mp"   
        and i: "(ti,vyi) \<in> set (zip (args t) (map Var ys))" 
      from *(1)[OF tl] obtain ts where l: "l = Var y" and t: "t = Fun f ts"  
        and lts: "length ts = n" by (cases t, auto)
      from i lts obtain i where i: "i < n" and ti: "ti = ts ! i" and yi: "vyi = Var (ys ! i)" 
        unfolding set_zip using \<open>length ys = n\<close> t by auto
      from match[OF tl] have mu_y: "\<mu> y = Fun f ts \<cdot> \<sigma>" unfolding l t by auto
      have yi: "vyi \<cdot> \<mu>' = args (\<mu> y) ! i" unfolding \<mu>'_def yi
        using i lts \<open>length ys = n\<close> *(3) mu_y 
        by (force split: option.splits simp: set_zip distinct_conv_nth)
      also have "\<dots> = ti \<cdot> \<sigma>" unfolding mu_y ti using i lts by auto
      finally show "ti \<cdot> \<sigma> = vyi \<cdot> \<mu>'" ..
    qed
  qed
qed auto

lemma mp_fail_pcorrect1:
  assumes "mp_fail mp" "\<sigma> :\<^sub>s sort_annotated |` tvars_match mp \<rightarrow> \<T>(C,X)"
  shows "\<not> match_complete_wrt \<sigma> mp"
  using assms
proof (induct mp rule: mp_fail.induct)
  case *: (mp_clash f ts g ls mp)
  {
    assume "length ts \<noteq> length ls" 
    hence "(map (\<lambda>t. t \<cdot> \<mu>) ls = map (\<lambda>t. t \<cdot> \<sigma>) ts) = False" for \<sigma> :: "('f,nat \<times> 's,'a)gsubst" and \<mu>
      by (metis length_map)
  } note len = this
  from * show ?case unfolding match_complete_wrt_def
    apply (auto simp: len split: prod.splits)
    using map_eq_imp_length_eq by force
next
  case *: (mp_clash' s t x mp)
  from conflicts(1)[OF *(1)]
  obtain po where po: "po \<in> poss s" "po \<in> poss t"
    and disj: "is_Fun (s |_ po) \<and> is_Fun (t |_ po) \<and> root (s |_ po) \<noteq> root (t |_ po) \<or>
    (\<exists>x y. s |_ po = Var x \<and> t |_ po = Var y \<and> snd x \<noteq> snd y)" 
    by auto
  show ?case 
  proof 
    assume "match_complete_wrt \<sigma> ({(s, Var x), (t, Var x)} \<union> mp)"
    from this[unfolded match_complete_wrt_def]
    have eq: "s \<cdot> \<sigma> |_po = t \<cdot> \<sigma> |_po" by auto
    from disj
    show False
    proof (elim disjE conjE exE)
      assume *: "is_Fun (s |_ po)" "is_Fun (t |_ po)" "root (s |_ po) \<noteq> root (t |_ po)"
      from eq have "root (s \<cdot> \<sigma> |_po) = root (t \<cdot> \<sigma> |_po)" by auto
      also have "root (s \<cdot> \<sigma> |_po) = root (s |_po \<cdot> \<sigma>)" using po by auto
      also have "\<dots> = root (s |_po)" using * by (cases "s |_ po", auto)
      also have "root (t \<cdot> \<sigma> |_po) = root (t |_po \<cdot> \<sigma>)" using po by (cases "t |_ po", auto)
      also have "\<dots> = root (t |_po)" using * by (cases "t |_ po", auto)
      finally show False using * by auto
    next
      fix y z assume y: "s |_ po = Var y" and z: "t |_ po = Var z" and ty: "snd y \<noteq> snd z"
      from y z eq po have yz: "\<sigma> y = \<sigma> z" by auto
      have "y \<in> vars_term s" "z \<in> vars_term t"
        using po[THEN vars_term_subt_at] y z by auto
      then
      have "\<sigma> y : snd y in \<T>(C,X)" "\<sigma> z : snd z in \<T>(C,X)"
        by (auto intro!: *(2)[THEN sorted_mapD] simp: hastype_restrict tvars_match_def)
      with ty yz show False by (auto simp: has_same_type)
    qed
  qed
qed

lemma mp_fail_pcorrect:
  assumes f: "mp_fail mp" and s: "\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)" and wf: "wf_match mp"
  shows "\<not> match_complete_wrt \<sigma> mp"
  apply (rule mp_fail_pcorrect1[OF f])
  apply (rule sorted_map_cmono[OF s])
  using wf by (auto intro!: subssetI simp: hastype_restrict wf_match_iff)

end

text \<open>For proving partial correctness we need further properties of the fixed parameters:
   We assume that \<open>m\<close> is sufficiently large and that there exists some constructor ground terms.
   Moreover \<open>inf_sort\<close> really computes whether a sort has terms of arbitrary size.
   Further all symbols in \<open>C\<close> must have sorts of \<open>S\<close>.
   Finally, \<open>Cl\<close> should precisely compute the constructors of a sort.\<close>

locale pattern_completeness_context_with_assms = pattern_completeness_context S C m Cl inf_sort cd_sort
  for S and C :: "('f,'s)ssig" 
    and m Cl inf_sort cd_sort +
  assumes not_empty_sort: "\<And> s. s \<in> S \<Longrightarrow> \<not> empty_sort C s"
    and C_sub_S: "\<And> f ss s. f : ss \<rightarrow> s in C \<Longrightarrow> insert s (set ss) \<subseteq> S"
    and m: "\<And> f ss s. f : ss \<rightarrow> s in C \<Longrightarrow> length ss \<le> m"
    and finite_C: "finite (dom C)"
    and inf_sort: "\<And>s. s \<in> S \<Longrightarrow> inf_sort s \<longleftrightarrow> \<not> finite_sort C s"
    and Cl: "\<And> s. set (Cl s) = {(f,ss). f : ss \<rightarrow> s in C}"
    and Cl_len: "\<And> \<sigma>. Ball (length ` snd ` set (Cl \<sigma>)) (\<lambda> a. a \<le> m)"
    and cd: "\<And>s. s \<in> S \<Longrightarrow> cd_sort s = card_of_sort C s"
begin

lemma sorts_non_empty: "s \<in> S \<Longrightarrow> \<exists> t. t : s in \<T>(C,\<emptyset>)"
  apply (drule not_empty_sort)
  by (auto elim: not_empty_sortE)

lemma inf_sort_not_bdd: "s \<in> S \<Longrightarrow> \<not> bdd_above (size ` {t . t : s in \<T>(C,\<emptyset>)}) \<longleftrightarrow> inf_sort s"
  apply (subst finite_sig_bdd_above_iff_finite[OF finite_C])
  by (auto simp: inf_sort finite_sort)

lemma C_nth_S: "f : ss \<rightarrow> s in C \<Longrightarrow> i < length ss \<Longrightarrow> ss!i \<in> S"
  using C_sub_S by force

lemmas subst_defs_set = 
  subst_pat_problem_set_def
  subst_match_problem_set_def

text \<open>Preservation of well-formedness\<close>

lemma mp_step_wf: "mp \<rightarrow>\<^sub>s mp' \<Longrightarrow> wf_match mp \<Longrightarrow> wf_match mp'" 
  unfolding wf_match_def tvars_match_def
proof (induct mp mp' rule: mp_step.induct)
  case (mp_decompose f ts ls mp)
  then show ?case by (auto dest!: set_zip_leftD)
next 
  case *: (mp_decompose' mp y f n mp' ys)
  from *(1) *(6)  
  show ?case 
    apply (auto dest!: set_zip_leftD) 
    subgoal for _ _ t by (cases t; force)
    subgoal for _ _ t by (cases t; force)
    done
qed auto

lemma pp_step_wf: "pp \<Rightarrow>\<^sub>s pp' \<Longrightarrow> wf_pat pp \<Longrightarrow> wf_pat pp'" 
  unfolding wf_pat_def
proof (induct pp pp' rule: pp_step.induct)
  case (pp_simp_mp mp mp' pp)
  then show ?case using mp_step_wf[of mp mp'] by auto
qed auto

theorem P_step_set_wf: "P \<Rrightarrow>\<^sub>s P' \<Longrightarrow> wf_pats P \<Longrightarrow> wf_pats P'" 
  unfolding wf_pats_def
proof (induct P P' rule: P_step_set.induct)
  case (P_simp pp pp' P)
  then show ?case using pp_step_wf[of pp pp'] by auto
next
  case *: (P_instantiate n p x P)
  let ?s = "snd x" 
  from * have sS: "?s \<in> S" and p: "wf_pat p" unfolding wf_pat_def wf_match_def tvars_pat_def by auto
  {
    fix \<tau>
    assume tau: "\<tau> \<in> \<tau>s n x" 
    from tau[unfolded \<tau>s_def \<tau>c_def, simplified]
    obtain f sorts where f: "f : sorts \<rightarrow> snd x in C" and \<tau>: "\<tau> = subst x (Fun f (map Var (zip [n..<n + length sorts] sorts)))" by auto
    let ?i = "length sorts" 
    let ?xs = "zip [n..<n + length sorts] sorts" 
    from C_sub_S[OF f] have sS: "?s \<in> S" and xs: "snd ` set ?xs \<subseteq> S" 
      unfolding set_conv_nth set_zip by auto
    {
      fix mp y
      assume mp: "mp \<in> p"  and "y \<in> tvars_match (subst_left \<tau> ` mp)"
      then obtain s t where y: "y \<in> vars (s \<cdot> \<tau>)" and st: "(s,t) \<in> mp" 
        unfolding tvars_match_def subst_left_def by auto
      from y have "y \<in> vars s \<union> set ?xs" unfolding vars_term_subst \<tau>
        by (auto simp: subst_def split: if_splits)
      hence "snd y \<in> snd ` vars s \<union> snd ` set ?xs" by auto
      also have "\<dots> \<subseteq> snd ` vars s \<union> S" using xs by auto
      also have "\<dots> \<subseteq> S" using p mp st
        unfolding wf_pat_def wf_match_def tvars_match_def by force
      finally have "snd y \<in> S" .
    }
    hence "wf_pat (subst_pat_problem_set \<tau> p)" 
      unfolding wf_pat_def wf_match_def subst_defs_set by auto
  }
  with * show ?case by auto
qed (auto simp: wf_pat_def)


text \<open>Soundness requires some preparations\<close>

definition \<sigma>g :: "nat\<times>'s \<Rightarrow> ('f,'v) term" where
  "\<sigma>g x = (SOME t. t : snd x in \<T>(C,\<emptyset>))"

lemma \<sigma>g: "\<sigma>g :\<^sub>s {x : \<iota> in sort_annotated. \<iota> \<in> S} \<rightarrow> \<T>(C,\<emptyset>)"
  using sorts_non_empty[THEN someI_ex]
  by (auto intro!: sorted_mapI simp: \<sigma>g_def)

lemma wf_pat_complete_iff:
  assumes "wf_pat pp"
  shows "pat_complete C pp \<longleftrightarrow> (\<forall>\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C). \<exists> mp \<in> pp. match_complete_wrt \<sigma> mp)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  show ?r
  proof (intro allI impI)
    fix \<sigma> :: "nat \<times> 's \<Rightarrow> _"
    assume s: "\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
    have "\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C)"
      apply (rule sorted_map_cmono[OF s])
      using assms by (auto intro!: subssetI simp: hastype_restrict wf_pat_iff)
    from pat_completeD[OF l this] show "\<exists>mp\<in>pp. match_complete_wrt \<sigma> mp".
  qed
next
  assume r: ?r
  show ?l
  proof (unfold pat_complete_def, safe)
    fix \<sigma> assume s: "\<sigma> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C)"
    define \<sigma>' where "\<sigma>' x \<equiv> if x \<in> tvars_pat pp then \<sigma> x else \<sigma>g x" for x
    have "\<sigma>' :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
      by (auto intro!: sorted_mapI sorted_mapD[OF s] sorted_mapD[OF \<sigma>g] simp: \<sigma>'_def hastype_restrict)
    from r[rule_format, OF this]
    obtain mp where mp: "mp \<in> pp" and m: "match_complete_wrt \<sigma>' mp" by auto
    have [simp]: "x \<in> tvars_match mp \<Longrightarrow> \<sigma> x = \<sigma>' x" for x using mp by (auto simp: \<sigma>'_def tvars_pat_def)
    from m have "match_complete_wrt \<sigma> mp" by (simp cong: match_complete_wrt_cong)
    with mp show "Bex pp (match_complete_wrt \<sigma>)" by auto
  qed
qed

lemma wf_pats_complete_iff:
  assumes wf: "wf_pats P"
  shows "pats_complete C P \<longleftrightarrow>
  (\<forall>\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C). \<forall>pp \<in> P. \<exists>mp \<in> pp. match_complete_wrt \<sigma> mp)"
    (is "?l \<longleftrightarrow> ?r")
proof safe
  fix \<sigma> pp assume s: "\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)" and pp: "pp \<in> P"
  have s2: "\<sigma> :\<^sub>s \<V> |` tvars_pats P \<rightarrow> \<T>(C)"
    apply (rule sorted_map_cmono[OF s])
    using wf
    by (auto intro!: subssetI simp: hastype_restrict wf_pats_def wf_pat_iff tvars_pats_def
        split: prod.splits)
  assume ?l
  with pp have comp: "pat_complete C pp" by auto
  from wf pp have "wf_pat pp" by (auto simp: wf_pats_def)
  from comp[unfolded wf_pat_complete_iff[OF this], rule_format, OF s]
  show "\<exists>mp \<in> pp. match_complete_wrt \<sigma> mp".
next
  fix pp assume pp: "pp \<in> P"
  assume r[rule_format]: ?r
  from wf pp have "wf_pat pp" by (auto simp: wf_pats_def)
  note * = wf_pat_complete_iff[OF this]
  show "pat_complete C pp"
    apply (unfold *) using r[OF _ pp] by auto
qed

lemma inf_var_conflictD: assumes "inf_var_conflict mp" 
  shows "\<exists> p s t x y. 
    (s,Var x) \<in> mp \<and> (t,Var x) \<in> mp \<and> s |_p = Var y \<and> s |_ p \<noteq> t |_p \<and>
   p \<in> poss s \<and> p \<in> poss t \<and> inf_sort (snd y)" 
proof -
  from assms[unfolded inf_var_conflict_def]
  obtain s t x y where "(s, Var x) \<in> mp \<and> (t, Var x) \<in> mp" and conf: "Conflict_Var s t y" and y: "inf_sort (snd y)" by blast
  with conflicts(2)[OF conf] show ?thesis by metis
qed

lemmas cg_term_vars = hastype_in_Term_empty_imp_vars

text \<open>Main partial correctness theorems on well-formed problems: the transformation rules do
  not change the semantics of a problem\<close>

lemma pp_step_pcorrect:
  "pp \<Rightarrow>\<^sub>s pp' \<Longrightarrow> wf_pat pp \<Longrightarrow> pat_complete C pp = pat_complete C pp'" 
proof (induct pp pp' rule: pp_step.induct)
  case *: (pp_simp_mp mp mp' pp)
  with mp_step_wf[OF *(1)]
  have "wf_pat (insert mp' pp)" by (auto simp: wf_pat_def)
  with *(2) mp_step_pcorrect[OF *(1)]
  show ?case by (auto simp: wf_pat_complete_iff)
next
  case *: (pp_remove_mp mp pp)
  from mp_fail_pcorrect[OF *(1)] *(2)
  show ?case by (auto simp: wf_pat_complete_iff wf_pat_def)
next
  case *: (pp_inf_var_conflict pp pp')
  note wf = \<open>wf_pat (pp \<union> pp')\<close> and fin = \<open>finite pp\<close>
  hence "wf_pat pp" and wfpp': "wf_pat pp'" by (auto simp: wf_pat_def)
  with wf have easy: "pat_complete C pp' \<Longrightarrow> pat_complete C (pp \<union> pp')"
    by (auto simp: wf_pat_complete_iff)
  {
    assume pp: "pat_complete C (pp \<union> pp')" 
    have "pat_complete C pp'" unfolding wf_pat_complete_iff[OF wfpp']
    proof (intro allI impI)
      fix \<delta>
      assume \<delta>: "\<delta> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)" 
      define conv :: "('f,unit) term \<Rightarrow> ('f, nat \<times> 's) term" where "conv t = t \<cdot> undefined" for t
      define conv' :: "('f, nat \<times> 's) term \<Rightarrow> ('f, unit) term" where "conv' t = t \<cdot> undefined" for t
      define confl' :: "('f, nat \<times> 's) term \<Rightarrow> ('f, nat \<times> 's)term \<Rightarrow> nat \<times> 's \<Rightarrow> bool" where "confl' = (\<lambda> sp tp y. 
           sp = Var y \<and> inf_sort (snd y) \<and> sp \<noteq> tp)" 
      define P1 where "P1 = (\<lambda> mp s t x y p. mp \<in> pp \<longrightarrow> (s, Var x) \<in> mp \<and> (t, Var x) \<in> mp \<and> p \<in> poss s \<and> p \<in> poss t \<and> confl' (s |_ p) (t |_ p) y)" 
      {
        fix mp
        assume "mp \<in> pp" 
        hence "inf_var_conflict mp" using * by auto
        from inf_var_conflictD[OF this] 
        have "\<exists> s t x y p. P1 mp s t x y p" unfolding P1_def confl'_def by force
      }
      hence "\<forall> mp. \<exists> s t x y p. P1 mp s t x y p" unfolding P1_def by blast
      from choice[OF this] obtain s where "\<forall> mp. \<exists> t x y p. P1 mp (s mp) t x y p" by blast
      from choice[OF this] obtain t where "\<forall> mp. \<exists> x y p. P1 mp (s mp) (t mp) x y p" by blast
      from choice[OF this] obtain x where "\<forall> mp. \<exists> y p. P1 mp (s mp) (t mp) (x mp) y p" by blast
      from choice[OF this] obtain y where "\<forall> mp. \<exists> p. P1 mp (s mp) (t mp) (x mp) (y mp) p" by blast
      from choice[OF this] obtain p where "\<forall> mp. P1 mp (s mp) (t mp) (x mp) (y mp) (p mp)" by blast
      note P1 = this[unfolded P1_def, rule_format]
      from *(2) have "finite (y ` pp)" by blast
      from ex_bij_betw_finite_nat[OF this] obtain index and n :: nat where 
        bij: "bij_betw index (y ` pp) {..<n}" 
        by (auto simp add: atLeast0LessThan)
      define var_ind :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> bool" where
        "var_ind i x = (x \<in> y ` pp \<and> index x \<in> {..<n} - {..<i})" for i x
      have [simp]: "var_ind n x = False" for x
        unfolding var_ind_def by auto  
      define cg_subst_ind :: "nat \<Rightarrow> ('f,nat \<times> 's)subst \<Rightarrow> bool" where
        "cg_subst_ind i \<sigma> = (\<forall> x. (var_ind i x \<longrightarrow> \<sigma> x = Var x)
            \<and> (\<not> var_ind i x \<longrightarrow> (vars_term (\<sigma> x) = {} \<and> (snd x \<in> S \<longrightarrow> \<sigma> x : snd x in \<T>(C,\<emptyset>))))
            \<and> (snd x \<in> S \<longrightarrow> \<not> inf_sort (snd x) \<longrightarrow> \<sigma> x = conv (\<delta> x)))" for i \<sigma>
      define confl :: "nat \<Rightarrow> ('f, nat \<times> 's) term \<Rightarrow> ('f, nat \<times> 's)term \<Rightarrow> bool" where "confl = (\<lambda> i sp tp. 
           (case (sp,tp) of (Var x, Var y) \<Rightarrow> x \<noteq> y \<and> var_ind i x \<and> var_ind i y
           | (Var x, Fun _ _) \<Rightarrow> var_ind i x
           | (Fun _ _, Var x) \<Rightarrow> var_ind i x
           | (Fun f ss, Fun g ts) \<Rightarrow> (f,length ss) \<noteq> (g,length ts)))"
      have confl_n: "confl n s t \<Longrightarrow> \<exists> f g ss ts. s = Fun f ss \<and> t = Fun g ts \<and> (f,length ss) \<noteq> (g,length ts)" for s t
        by (cases s; cases t; auto simp: confl_def)
      {
        fix i x
        assume "var_ind i x" 
        from this[unfolded var_ind_def] obtain i 
          where z: "x \<in> y ` pp" "index x = i" by blast 
        from z obtain mp where "mp \<in> pp" and "index (y mp) = i" and "x = y mp" by auto
        with P1[OF this(1), unfolded confl'_def] have inf: "inf_sort (snd x)" by auto
      } note var_ind_inf = this
      {
        fix i
        assume "i \<le> n"
        hence "\<exists> \<sigma>. cg_subst_ind i \<sigma> \<and> (\<forall> mp \<in> pp. \<exists> p. p \<in> poss (s mp \<cdot> \<sigma>) \<and> p \<in> poss (t mp \<cdot> \<sigma>) \<and> confl i (s mp \<cdot> \<sigma> |_ p) (t mp \<cdot> \<sigma> |_ p))" 
        proof (induction i)
          case 0
          define \<sigma> where "\<sigma> x = (if var_ind 0 x then Var x else if snd x \<in> S then conv (\<delta> x) else Fun undefined [])" for x
          have \<sigma>: "cg_subst_ind 0 \<sigma>" unfolding cg_subst_ind_def
          proof (intro allI impI conjI)
            fix x
            show "var_ind 0 x \<Longrightarrow> \<sigma> x = Var x" unfolding \<sigma>_def by auto
            show "\<not> var_ind 0 x \<Longrightarrow> vars (\<sigma> x) = {}" 
              unfolding \<sigma>_def conv_def using \<delta>[THEN sorted_mapD, of x] 
              by (auto simp: vars_term_subst  hastype_in_Term_empty_imp_vars)
            show "\<not> var_ind 0 x \<Longrightarrow> snd x \<in> S \<Longrightarrow> \<sigma> x : snd x in \<T>(C,\<emptyset>)" 
              using \<delta>[THEN sorted_mapD, of x]
              unfolding \<sigma>_def conv_def by (auto simp: \<sigma>_def intro: type_conversion)
            show "snd x \<in> S \<Longrightarrow> \<not> inf_sort (snd x) \<Longrightarrow> \<sigma> x = conv (\<delta> x)" 
              unfolding \<sigma>_def by (auto dest: var_ind_inf)
          qed            
          show ?case
          proof (rule exI, rule conjI[OF \<sigma>], intro ballI exI conjI)
            fix mp
            assume mp: "mp \<in> pp" 
            note P1 = P1[OF this]
            from mp have mem: "y mp \<in> y ` pp" by auto
            with bij have y: "index (y mp) \<in> {..<n}" by (metis bij_betw_apply)
            hence y0: "var_ind 0 (y mp)" using mem unfolding var_ind_def by auto
            show "p mp \<in> poss (s mp \<cdot> \<sigma>)" using P1 by auto
            show "p mp \<in> poss (t mp \<cdot> \<sigma>)" using P1 by auto
            let ?t = "t mp |_ p mp" 
            define c where "c = confl 0 (s mp \<cdot> \<sigma> |_ p mp) (t mp \<cdot> \<sigma> |_ p mp)" 
            have "c = confl 0 (s mp |_ p mp \<cdot> \<sigma>) (?t \<cdot> \<sigma>)" 
              using P1 unfolding c_def by auto
            also have s: "s mp |_ p mp = Var (y mp)" using P1 unfolding confl'_def by auto
            also have "\<dots> \<cdot> \<sigma> = Var (y mp)" using y0 unfolding \<sigma>_def by auto
            also have "confl 0 (Var (y mp)) (?t \<cdot> \<sigma>)" 
            proof (cases "?t \<cdot> \<sigma>")
              case Fun
              thus ?thesis using y0 unfolding confl_def by auto
            next
              case (Var z)
              then obtain u where t: "?t = Var u" and ssig: "\<sigma> u = Var z" 
                by (cases ?t, auto)
              from P1[unfolded s] have "confl' (Var (y mp)) ?t (y mp)" by auto
              from this[unfolded confl'_def t] have uy: "y mp \<noteq> u" by auto
              show ?thesis
              proof (cases "var_ind 0 u")
                case True
                with y0 uy show ?thesis unfolding t \<sigma>_def confl_def by auto
              next
                case False
                with ssig[unfolded \<sigma>_def] have uS: "snd u \<in> S" and contra: "conv (\<delta> u) = Var z" 
                  by (auto split: if_splits)
                from \<delta>[THEN sorted_mapD, of u] uS contra
                have False by (cases "\<delta> u", auto simp: conv_def)
                thus ?thesis ..
              qed
            qed
            finally show "confl 0 (s mp \<cdot> \<sigma> |_ p mp) (t mp \<cdot> \<sigma> |_ p mp)" unfolding c_def .
          qed
        next
          case (Suc i)
          then obtain \<sigma> where \<sigma>: "cg_subst_ind i \<sigma>" and confl: "(\<forall>mp\<in>pp. \<exists>p. p \<in> poss (s mp \<cdot> \<sigma>) \<and> p \<in> poss (t mp \<cdot> \<sigma>) \<and> confl i (s mp \<cdot> \<sigma> |_ p) (t mp \<cdot> \<sigma> |_ p))" 
            by auto
          from Suc have "i \<in> {..< n}" and i: "i < n" by auto
          with bij obtain z where z: "z \<in> y ` pp" "index z = i" unfolding bij_betw_def by (metis imageE)
          {
            from z obtain mp where "mp \<in> pp" and "index (y mp) = i" and "z = y mp" by auto
            with P1[OF this(1), unfolded confl'_def] have inf: "inf_sort (snd z)" 
              and *: "p mp \<in> poss (s mp)" "s mp |_ p mp = Var z" "(s mp, Var (x mp)) \<in> mp"
              by auto
            from *(1,2) have "z \<in> vars (s mp)" using vars_term_subt_at by fastforce
            with *(3) have "z \<in> tvars_match mp" unfolding tvars_match_def by force
            with \<open>mp \<in> pp\<close> wf have "snd z \<in> S" unfolding wf_pat_def wf_match_def by auto
            from not_bdd_above_natD[OF inf_sort_not_bdd[OF this, THEN iffD2, OF inf]]
              sorts_non_empty[OF this]
            have "\<And> n. \<exists> t. t : snd z in \<T>(C,\<emptyset>::nat\<times>'s\<rightharpoonup>_) \<and> n < size t" by auto
            note this inf
          } note z_inf = this
            (* define d as 1 + maximal size of all s- and t-terms in pp \<sigma> *)
          define all_st where "all_st = (\<lambda> mp. s mp \<cdot> \<sigma>) ` pp \<union> (\<lambda> mp. t mp \<cdot> \<sigma>) ` pp" 
          have fin_all_st: "finite all_st" unfolding all_st_def using *(2) by simp
          define d :: nat where "d = Suc (Max (size ` all_st))" 
          from z_inf(1)[of d]
          obtain u :: "('f,nat\<times>'s) term"
            where u: "u : snd z in \<T>(C,\<emptyset>)" and du: "d \<le> size u" by auto
          have vars_u: "vars u = {}" by (rule cg_term_vars[OF u])
          define \<sigma>' where "\<sigma>' x = (if x = z then u else \<sigma> x)" for x
          have \<sigma>'_def': "\<sigma>' x = (if x \<in> y ` pp \<and> index x = i then u else \<sigma> x)" for x
            unfolding \<sigma>'_def by (rule if_cong, insert bij z, auto simp: bij_betw_def inj_on_def) 
          have var_ind_conv: "var_ind i x = (x = z \<or> var_ind (Suc i) x)" for x
          proof
            assume "x = z \<or> var_ind (Suc i) x" 
            thus "var_ind i x" using z i unfolding var_ind_def by auto
          next
            assume "var_ind i x" 
            hence x: "x \<in> y ` pp" "index x \<in> {..<n} - {..<i}" unfolding var_ind_def by auto
            with i have "index x = i \<or> index x \<in> {..<n} - {..<Suc i}" by auto
            thus "x = z \<or> var_ind (Suc i) x"
            proof
              assume "index x = i" 
              with x(1) z bij have "x = z" by (auto simp: bij_betw_def inj_on_def)
              thus ?thesis by auto
            qed (insert x, auto simp: var_ind_def)
          qed
          have [simp]: "var_ind i z" unfolding var_ind_conv by auto
          have [simp]: "var_ind (Suc i) z = False" unfolding var_ind_def using z by auto
          have \<sigma>z[simp]: "\<sigma> z = Var z" using \<sigma>[unfolded cg_subst_ind_def, rule_format, of z] by auto
          have \<sigma>'_upd: "\<sigma>' = \<sigma>(z := u)" unfolding \<sigma>'_def by (intro ext, auto)
          have \<sigma>'_comp: "\<sigma>' = \<sigma> \<circ>\<^sub>s Var(z := u)" unfolding subst_compose_def \<sigma>'_upd
          proof (intro ext)
            fix x
            show "(\<sigma>(z := u)) x = \<sigma> x \<cdot> Var(z := u)" 
            proof (cases "x = z")
              case False
              hence "\<sigma> x \<cdot> (Var(z := u)) = \<sigma> x \<cdot> Var" 
              proof (intro term_subst_eq)
                fix y
                assume y: "y \<in> vars (\<sigma> x)" 
                show "(Var(z := u)) y = Var y" 
                proof (cases "var_ind i x")
                  case True
                  with \<sigma>[unfolded cg_subst_ind_def, rule_format, of x]
                  have "\<sigma> x = Var x" by auto
                  with False y show ?thesis by auto
                next
                  case False
                  with \<sigma>[unfolded cg_subst_ind_def, rule_format, of x]
                  have "vars (\<sigma> x) = {}" by auto
                  with y show ?thesis by auto
                qed
              qed
              thus ?thesis by auto
            qed simp
          qed
          have \<sigma>': "cg_subst_ind (Suc i) \<sigma>'" unfolding cg_subst_ind_def
          proof (intro allI conjI impI)
            fix x
            assume "var_ind (Suc i) x" 
            hence "var_ind i x" and diff: "index x \<noteq> i" unfolding var_ind_def by auto
            hence "\<sigma> x = Var x" using \<sigma>[unfolded cg_subst_ind_def] by blast
            thus "\<sigma>' x = Var x" unfolding \<sigma>'_def' using diff by auto
          next
            fix x
            assume "\<not> var_ind (Suc i) x" and "snd x \<in> S" 
            thus "\<sigma>' x : snd x in \<T>(C,\<emptyset>)" 
              using \<sigma>[unfolded cg_subst_ind_def, rule_format, of x] u
              unfolding \<sigma>'_def var_ind_conv by auto
          next
            fix x
            assume "\<not> var_ind (Suc i) x"  
            hence "x = z \<or> \<not> var_ind i x" unfolding var_ind_conv by auto
            thus "vars (\<sigma>' x) = {}" unfolding \<sigma>'_upd using \<sigma>[unfolded cg_subst_ind_def, rule_format, of x] vars_u by auto
          next
            fix x :: "nat \<times> 's" 
            assume *: "snd x \<in> S" "\<not> inf_sort (snd x)" 
            with z_inf(2) have "x \<noteq> z" by auto
            hence "\<sigma>' x = \<sigma> x" unfolding \<sigma>'_def by auto
            thus "\<sigma>' x = conv (\<delta> x)" using \<sigma>[unfolded cg_subst_ind_def, rule_format, of x] * by auto
          qed
          show ?case
          proof (intro exI[of _ \<sigma>'] conjI \<sigma>' ballI)
            fix mp
            assume mp: "mp \<in> pp" 
            define s' where "s' = s mp \<cdot> \<sigma>" 
            define t' where "t' = t mp \<cdot> \<sigma>" 
            from confl[rule_format, OF mp]
            obtain p where p: "p \<in> poss s'" "p \<in> poss t'" and confl: "confl i (s' |_ p) (t' |_ p)" by (auto simp: s'_def t'_def)
            {
              fix s' t' :: "('f, nat \<times> 's) term" and p f ss x
              assume *: "(s' |_ p, t' |_p) = (Fun f ss, Var x)" "var_ind i x" and p: "p \<in> poss s'" "p \<in> poss t'" 
                and range_all_st: "s' \<in> all_st" 
              hence s': "s' \<cdot> Var(z := u) |_ p = Fun f ss \<cdot> Var(z := u)" (is "_ = ?s")
                and t': "t' \<cdot> Var(z := u) |_ p = (if x = z then u else Var x)" using p by auto
              from range_all_st[unfolded all_st_def] 
              have range\<sigma>: "\<exists> S. s' = S \<cdot> \<sigma>" by auto
              define s where "s = ?s"
              have "\<exists>p. p \<in> poss (s' \<cdot> Var(z := u)) \<and> p \<in> poss (t' \<cdot> Var(z := u)) \<and> confl (Suc i) (s' \<cdot> Var(z := u) |_ p) (t' \<cdot> Var(z := u) |_ p)" 
              proof (cases "x = z")
                case False
                thus ?thesis using * p unfolding s' t' by (intro exI[of _ p], auto simp: confl_def var_ind_conv)
              next
                case True
                hence t': "t' \<cdot> Var(z := u) |_ p = u" unfolding t' by auto
                have "\<exists> p'. p' \<in> poss u \<and> p' \<in> poss s \<and> confl (Suc i) (s |_ p') (u |_ p')" 
                proof (cases "\<exists> x. x \<in> vars s \<and> var_ind (Suc i) x")
                  case True
                  then obtain x where xs: "x \<in> vars s" and x: "var_ind (Suc i) x" by auto
                  from xs obtain p' where p': "p' \<in> poss s" and sp: "s |_ p' = Var x" by (metis vars_term_poss_subt_at)
                  from p' sp vars_u show ?thesis 
                  proof (induct u arbitrary: p' s) 
                    case (Fun f us p' s)
                    show ?case
                    proof (cases s)
                      case (Var y)
                      with Fun have s: "s = Var x" by auto
                      with x show ?thesis by (intro exI[of _ Nil], auto simp: confl_def)
                    next
                      case s: (Fun g ss)
                      with Fun obtain j p where p: "p' = j # p" "j < length ss" "p \<in> poss (ss ! j)" "(ss ! j) |_ p = Var x" by auto
                      show ?thesis
                      proof (cases "(f,length us) = (g,length ss)")
                        case False
                        thus ?thesis by (intro exI[of _ Nil], auto simp: s confl_def)
                      next
                        case True
                        with p have j: "j < length us" by auto
                        hence usj: "us ! j \<in> set us" by auto
                        with Fun have "vars (us ! j) = {}" by auto
                        from Fun(1)[OF usj p(3,4) this] obtain p' where 
                          "p' \<in> poss (us ! j) \<and> p' \<in> poss (ss ! j) \<and> confl (Suc i) (ss ! j |_ p') (us ! j |_ p')" by auto
                        thus ?thesis using j p by (intro exI[of _ "j # p'"], auto simp: s)
                      qed
                    qed
                  qed auto
                next
                  case False
                  from * have fss: "Fun f ss = s' |_ p" by auto 
                  from range\<sigma> obtain S where sS: "s' = S \<cdot> \<sigma>" by auto
                  from p have "vars (s' |_ p) \<subseteq> vars s'" by (metis vars_term_subt_at)
                  also have "\<dots> = (\<Union>y\<in>vars S. vars (\<sigma> y))" unfolding sS by (simp add: vars_term_subst)
                  also have "\<dots> \<subseteq> (\<Union>y\<in>vars S. Collect (var_ind i))" 
                  proof -
                    {
                      fix x y
                      assume "x \<in> vars (\<sigma> y)" 
                      hence "var_ind i x" 
                        using \<sigma>[unfolded cg_subst_ind_def, rule_format, of y] by auto
                    }
                    thus ?thesis by auto
                  qed
                  finally have sub: "vars (s' |_ p) \<subseteq> Collect (var_ind i)" by blast
                  have "vars s = vars (s' |_ p \<cdot> Var(z := u))" unfolding s_def s' fss by auto 
                  also have "\<dots> = \<Union> (vars ` Var(z := u) ` vars (s' |_ p))" by (simp add: vars_term_subst) 
                  also have "\<dots> \<subseteq> \<Union> (vars ` Var(z := u) ` Collect (var_ind i))" using sub by auto
                  also have "\<dots> \<subseteq> Collect (var_ind (Suc i))" 
                    by (auto simp: vars_u var_ind_conv)
                  finally have vars_s: "vars s = {}" using False by auto
                      (* so u and s are ground terms; we will show that they differ and hence a 
                   clash must exist *)
                  {
                    assume "s = u" 
                    from this[unfolded s_def fss]
                    have eq: "s' |_ p \<cdot> Var(z := u) = u" by auto
                    have False
                    proof (cases "z \<in> vars (s' |_ p)")
                      case True
                      have diff: "s' |_ p \<noteq> Var z" using * by auto 
                      from True obtain C where id: "s' |_ p = C \<langle> Var z \<rangle>" 
                        by (metis ctxt_supt_id vars_term_poss_subt_at)
                      with diff have diff: "C \<noteq> Hole" by (cases C, auto)
                      from eq[unfolded id, simplified] diff
                      obtain C where "C\<langle>u\<rangle> = u" and "C \<noteq> Hole" by (cases C; force)
                      from arg_cong[OF this(1), of size] this(2) show False 
                        by (simp add: less_not_refl2 size_ne_ctxt)
                    next
                      case False
                      have size: "size s' \<in> size ` all_st" using range_all_st by auto
                      from False have "s' |_ p \<cdot> Var(z := u) = s' |_ p \<cdot> Var" 
                        by (intro term_subst_eq, auto)
                      with eq have eq: "s' |_ p = u" by auto
                      hence "size u = size (s' |_ p)" by auto
                      also have "\<dots> \<le> size s'" using p(1) 
                        by (rule subt_size)
                      also have "\<dots> \<le> Max (size ` all_st)" 
                        using size fin_all_st by simp
                      also have "\<dots> < d" unfolding d_def by simp
                      also have "\<dots> \<le> size u" using du .
                      finally show False by simp
                    qed
                  }
                  hence "s \<noteq> u" by auto
                  with vars_s vars_u
                  show ?thesis 
                  proof (induct s arbitrary: u)
                    case s: (Fun f ss u)
                    then obtain g us where u: "u = Fun g us" by (cases u, auto)
                    show ?case
                    proof (cases "(f,length ss) = (g,length us)")
                      case False
                      thus ?thesis unfolding u by (intro exI[of _ Nil], auto simp: confl_def)
                    next
                      case True
                      with s(4)[unfolded u] have "\<exists> j < length us. ss ! j \<noteq> us ! j" 
                        by (auto simp: list_eq_nth_eq)
                      then obtain j where j: "j < length us" and diff: "ss ! j \<noteq> us ! j" by auto
                      from j True have mem: "ss ! j \<in> set ss" "us ! j \<in> set us" by auto
                      with s(2-) u have "vars (ss ! j) = {}" "vars (us ! j) = {}" by auto
                      from s(1)[OF mem(1) this diff] obtain p' where
                        "p' \<in> poss (us ! j) \<and> p' \<in> poss (ss ! j) \<and> confl (Suc i) (ss ! j |_ p') (us ! j |_ p')" 
                        by blast
                      thus ?thesis unfolding u using True j by (intro exI[of _ "j # p'"], auto)
                    qed
                  qed auto
                qed
                then obtain p' where p': "p' \<in> poss u" "p' \<in> poss s" and confl: "confl (Suc i) (s |_ p') (u |_ p')" by auto
                have s'': "s' \<cdot> Var(z := u) |_ (p @ p') = s |_ p'" unfolding s_def s'[symmetric] using p p' by auto
                have t'': "t' \<cdot> Var(z := u) |_ (p @ p') = u |_ p'" using t' p p' by auto
                show ?thesis 
                proof (intro exI[of _ "p @ p'"], unfold s'' t'', intro conjI confl)
                  have "p \<in> poss (s' \<cdot> Var(z := u))" using p by auto
                  moreover have "p' \<in> poss ((s' \<cdot> Var(z := u)) |_ p)" using s' p' p unfolding s_def by auto
                  ultimately show "p @ p' \<in> poss (s' \<cdot> Var(z := u))" by simp
                  have "p \<in> poss (t' \<cdot> Var(z := u))" using p by auto
                  moreover have "p' \<in> poss ((t' \<cdot> Var(z := u)) |_ p)" using t' p' p by auto
                  ultimately show "p @ p' \<in> poss (t' \<cdot> Var(z := u))" by simp
                qed
              qed
            } note main = this
            consider (FF) f g ss ts where "(s' |_ p, t' |_ p) = (Fun f ss, Fun g ts)" "(f,length ss) \<noteq> (g,length ts)" 
              | (FV) f ss x where "(s' |_ p, t' |_ p) = (Fun f ss, Var x)" "var_ind i x"
              | (VF) f ss x where "(s' |_ p, t' |_ p) = (Var x, Fun f ss)" "var_ind i x" 
              | (VV) x x' where "(s' |_ p, t' |_ p) = (Var x, Var x')" "x \<noteq> x'" "var_ind i x" "var_ind i x'" 
              using confl by (auto simp: confl_def split: term.splits)
            hence "\<exists>p. p \<in> poss (s' \<cdot> Var(z := u)) \<and> p \<in> poss (t' \<cdot> Var(z := u)) \<and> confl (Suc i) (s' \<cdot> Var(z := u) |_ p) (t' \<cdot> Var(z := u) |_ p)" 
            proof cases
              case (FF f g ss ts)
              thus ?thesis using p by (intro exI[of _ p], auto simp: confl_def)
            next
              case (FV f ss x)
              have "s' \<in> all_st" unfolding s'_def using mp all_st_def by auto
              from main[OF FV p this] show ?thesis by auto
            next
              case (VF f ss x)
              have t': "t' \<in> all_st" unfolding t'_def using mp all_st_def by auto
              from VF have "(t' |_ p, s' |_ p) = (Fun f ss, Var x)" "var_ind i x" by auto
              from main[OF this p(2,1) t'] 
              obtain p where "p \<in> poss (t' \<cdot> Var(z := u))" "p \<in> poss (s' \<cdot> Var(z := u))" "confl (Suc i) (t' \<cdot> Var(z := u) |_ p) (s' \<cdot> Var(z := u) |_ p)"
                by auto
              thus ?thesis by (intro exI[of _ p], auto simp: confl_def split: term.splits)
            next
              case (VV x x')
              thus ?thesis using p vars_u by (intro exI[of _ p], cases u, auto simp: confl_def var_ind_conv)
            qed
            thus "\<exists>p. p \<in> poss (s mp \<cdot> \<sigma>') \<and> p \<in> poss (t mp \<cdot> \<sigma>') \<and> confl (Suc i) (s mp \<cdot> \<sigma>' |_ p) (t mp \<cdot> \<sigma>' |_ p)" 
              unfolding \<sigma>'_comp subst_subst_compose s'_def t'_def by auto
          qed
        qed
      }
      from this[of n]
      obtain \<sigma> where \<sigma>: "cg_subst_ind n \<sigma>" and confl: "\<And> mp. mp \<in> pp \<Longrightarrow> \<exists>p. p \<in> poss (s mp \<cdot> \<sigma>) \<and> p \<in> poss (t mp \<cdot> \<sigma>) \<and> confl n (s mp \<cdot> \<sigma> |_ p) (t mp \<cdot> \<sigma> |_ p)" 
        by blast
      define \<sigma>' :: "('f,nat \<times> 's,unit)gsubst" where "\<sigma>' x = conv' (Var x)" for x
      let ?\<sigma> = "\<sigma> \<circ>\<^sub>s \<sigma>'" 
      {
        fix x :: "nat \<times> 's" 
        assume *: "snd x \<in> S" "\<not> inf_sort (snd x)" 
        from \<delta>[THEN sorted_mapD, of x] * have "\<delta> x : snd x in \<T>(C,\<emptyset>)" by auto
        hence vars: "vars (\<delta> x) = {}" by (simp add: hastype_in_Term_empty_imp_vars)
        from * \<sigma>[unfolded cg_subst_ind_def] have "\<sigma> x = conv (\<delta> x)" by blast
        hence "?\<sigma> x = \<delta> x \<cdot> (undefined \<circ>\<^sub>s \<sigma>')" by (simp add: subst_compose_def conv_def subst_subst)
        also have "\<dots> = \<delta> x" by (rule ground_term_subst[OF vars]) 
        finally have "?\<sigma> x = \<delta> x" .
      } note \<sigma>\<delta> = this
      have "?\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
      proof (intro sorted_mapI, unfold subst_compose_def hastype_in_restrict_sset conj_imp_eq_imp_imp)
        fix x :: "nat \<times> 's" and \<iota>
        assume "x : \<iota> in \<V>" and "\<iota> \<in> S"
        then have "snd x = \<iota>" "\<iota> \<in> S" by auto
        with \<sigma>[unfolded cg_subst_ind_def, rule_format, of x]
        have "\<sigma> x : \<iota> in \<T>(C,\<emptyset>)" by auto
        thus "\<sigma> x \<cdot> \<sigma>' : \<iota> in \<T>(C,\<emptyset>)" by (rule type_conversion)
      qed
      from pp[unfolded wf_pat_complete_iff[OF wf] match_complete_wrt_def, rule_format, OF this]
      obtain mp \<mu> where mp: "mp \<in> pp \<union> pp'" and match: "\<And> ti li. (ti, li)\<in> mp \<Longrightarrow> ti \<cdot> ?\<sigma> = li \<cdot> \<mu>" by force
      {
        assume mp: "mp \<in> pp" 
        from P1[OF this(1)] 
        have "(s mp, Var (x mp)) \<in> mp" "(t mp, Var (x mp)) \<in> mp" by auto
        from match[OF this(1)] match[OF this(2)] have ident: "s mp \<cdot> ?\<sigma> = t mp \<cdot> ?\<sigma>" by auto
        from confl[OF mp] obtain p 
          where p: "p \<in> poss (s mp \<cdot> \<sigma>)" "p \<in> poss (t mp \<cdot> \<sigma>)" and confl: "confl n (s mp \<cdot> \<sigma> |_ p) (t mp \<cdot> \<sigma> |_ p)" 
          by auto
        let ?s = "s mp \<cdot> \<sigma>" let ?t = "t mp \<cdot> \<sigma>" 
        from confl_n[OF confl] obtain f g ss ts where 
          confl: "?s |_p = Fun f ss" "?t |_p = Fun g ts" and diff: "(f,length ss) \<noteq> (g,length ts)" by auto
        define s' where "s' = s mp \<cdot> \<sigma>" 
        define t' where "t' = t mp \<cdot> \<sigma>" 
        from confl p ident 
        have False 
          unfolding subst_subst_compose s'_def[symmetric] t'_def[symmetric]
        proof (induction p arbitrary: s' t')
          case Nil
          then show ?case using diff by (auto simp: list_eq_nth_eq)
        next
          case (Cons i p s t)
          from Cons obtain h1 us1 where s: "s = Fun h1 us1" by (cases s, auto)
          from Cons obtain h2 us2 where t: "t = Fun h2 us2" by (cases t, auto)
          from Cons(2,4)[unfolded s] have si: "(us1 ! i) |_ p = Fun f ss" "p \<in> poss (us1 ! i)" and i1: "i < length us1" by auto
          from Cons(3,5)[unfolded t] have ti: "(us2 ! i) |_ p = Fun g ts" "p \<in> poss (us2 ! i)" and i2: "i < length us2" by auto
          from Cons(6)[unfolded s t] i1 i2 have " us1 ! i \<cdot> \<sigma>' = us2 ! i \<cdot> \<sigma>'" by (auto simp: list_eq_nth_eq)
          from Cons.IH[OF si(1) ti(1) si(2) ti(2) this]
          show False .
        qed
      }
      with mp have mp: "mp \<in> pp'" by auto
      show "Bex pp' (match_complete_wrt \<delta>)" 
        unfolding match_complete_wrt_def
      proof (intro bexI[OF _ mp] exI[of _ \<mu>] ballI, clarify)
        fix ti li
        assume tl: "(ti, li) \<in> mp" 
        have "ti \<cdot> \<delta> = ti \<cdot> ?\<sigma>" 
        proof (intro term_subst_eq, rule sym, rule \<sigma>\<delta>)
          fix x
          assume x: "x \<in> vars ti"
          from *(3) x tl mp show "\<not> inf_sort (snd x)" by (auto simp: tvars_pat_def tvars_match_def) 
          from *(5) x tl mp show "snd x \<in> S" 
            unfolding wf_pat_def wf_match_def tvars_match_def by auto
        qed
        also have "\<dots> = li \<cdot> \<mu>" using match[OF tl] .
        finally show "ti \<cdot> \<delta> = li \<cdot> \<mu>" .
      qed
    qed
  }
  with easy show ?case by auto
qed

lemma pp_success_pcorrect: "pp_success pp \<Longrightarrow> pat_complete C pp" 
  by (induct pp rule: pp_success.induct, auto simp: pat_complete_def match_complete_wrt_def)

theorem P_step_set_pcorrect:
  "P \<Rrightarrow>\<^sub>s P' \<Longrightarrow> wf_pats P \<Longrightarrow> pats_complete C P \<longleftrightarrow> pats_complete C P'"
proof (induct P P' rule: P_step_set.induct)
  case (P_fail P)
  with \<sigma>g show ?case by (auto simp: wf_pats_complete_iff)
next
  case *: (P_simp pp pp' P)
  with pp_step_wf have "wf_pat pp" "wf_pats P" "wf_pats (insert pp P)" "wf_pats (insert pp' P)"
    by (auto simp: wf_pats_def)
  with pp_step_pcorrect[OF *(1)] show ?case
    by (auto simp: wf_pat_complete_iff wf_pats_complete_iff wf_pats_def)
next
  case *: (P_remove_pp pp P)
  with pp_step_wf have "wf_pat pp" "wf_pats P" "wf_pats (insert pp P)" by (auto simp: wf_pats_def)
  then show ?case using pp_success_pcorrect[OF *(1)]
    by (auto simp: wf_pats_complete_iff wf_pat_complete_iff)
next
  case *: (P_instantiate n pp x P)
  note wfppP = \<open>wf_pats (insert pp P)\<close>
  then have wfpp: "wf_pat pp" and wfP: "wf_pats P" by (auto simp: wf_pats_def)
  (* This is the step where well-formedness is essential *)
  from wfpp *(2) have x: "snd x \<in> S"
    unfolding tvars_pat_def tvars_match_def wf_pat_def wf_match_def by force
  note def = wf_pat_complete_iff[unfolded match_complete_wrt_def]
  define P' where "P' = {subst_pat_problem_set \<tau> pp |. \<tau> \<in> \<tau>s n x}"
  show ?case
    apply (fold P'_def)
  proof (rule ball_insert_un_cong, standard)
    assume complete: "Ball P' (pat_complete C)"
    show "pat_complete C pp" unfolding def[OF wfpp]
    proof (intro allI impI)
      fix \<sigma>
      assume cg: "\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
      from sorted_mapD[OF this] x
      have "\<sigma> x : snd x in \<T>(C)" by auto
      then obtain f ts \<sigma>s where f: "f : \<sigma>s \<rightarrow> snd x in C"
        and args: "ts :\<^sub>l \<sigma>s in \<T>(C)"
        and \<sigma>x: "\<sigma> x = Fun f ts"
        by (induct, auto)
      from f have f: "f : \<sigma>s \<rightarrow> snd x in C"
        by (meson fun_hastype_def)
      let ?l = "length ts" 
      from args have len: "length \<sigma>s = ?l" by (simp add: list_all2_lengthD)
      have l: "?l \<le> m" using m[OF f] len by auto
      have \<sigma>sS: "\<forall>\<iota> \<in> set \<sigma>s. \<iota> \<in> S" using C_sub_S f by auto
      define \<sigma>' where "\<sigma>' = (\<lambda> ys. let y = fst ys in if n \<le> y \<and> y < n + ?l \<and> \<sigma>s ! (y - n) = snd ys then ts ! (y - n) else \<sigma> ys)" 
      have cg: "\<sigma>' :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
      proof (intro sorted_mapI, unfold hastype_in_restrict_sset conj_imp_eq_imp_imp)
        fix ys :: "nat \<times> 's" and \<iota>
        assume "ys : \<iota> in \<V>" and "\<iota> \<in> S"
        then have [simp]: "\<iota> = snd ys" and ysS: "snd ys \<in> S" by auto
        show "\<sigma>' ys : \<iota> in \<T>(C)" 
        proof (cases "\<sigma>' ys = \<sigma> ys")
          case True
          thus ?thesis using cg ysS by (auto simp: sorted_mapD)
        next
          case False
          obtain y s where ys: "ys = (y,s)" by force
          with False have y: "y - n < ?l" "n \<le> y" "y < n + ?l" and arg: "\<sigma>s ! (y - n) = s"
            and \<sigma>': "\<sigma>' ys = ts ! (y - n)" 
            unfolding \<sigma>'_def Let_def by (auto split: if_splits)
          show ?thesis
            using \<sigma>' len list_all2_nthD[OF args y(1)]
            by (auto simp: ys arg[symmetric])
        qed
      qed
      define \<tau> where "\<tau> = subst x (Fun f (map Var (zip [n..<n + ?l] \<sigma>s)))"
      have "\<tau> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C,{x : \<iota> in \<V>. \<iota> \<in> S})"
        using Fun_hastypeI[OF f, of "{x : \<iota> in \<V>. \<iota> \<in> S}" "map Var (zip [n..<n + ?l] \<sigma>s)"] \<sigma>sS wfpp
        by (auto intro!: sorted_mapI
            simp: \<tau>_def subst_def len[symmetric] list_all2_conv_all_nth hastype_restrict wf_pat_iff)
      from wf_pat_subst[OF this]
      have wf2: "wf_pat (subst_pat_problem_set \<tau> pp)".
      from f have "\<tau> \<in> \<tau>s n x" unfolding \<tau>s_def \<tau>_def \<tau>c_def using len[symmetric] by auto
      hence "pat_complete C (subst_pat_problem_set \<tau> pp)" using complete by (auto simp: P'_def)
      from this[unfolded def[OF wf2], rule_format, OF cg]
      obtain tl \<mu> where tl: "tl \<in> subst_pat_problem_set \<tau> pp" 
        and match: "\<And> ti li. (ti, li) \<in> tl \<Longrightarrow> ti \<cdot> \<sigma>' = li \<cdot> \<mu>" by force          
      from tl[unfolded subst_defs_set subst_left_def set_map]
      obtain tl' where tl': "tl' \<in> pp" and tl: "tl = {(t' \<cdot> \<tau>, l) |. (t',l) \<in> tl'}" by auto 
      show "\<exists>tl\<in> pp. \<exists>\<mu>. \<forall>(ti, li)\<in> tl. ti \<cdot> \<sigma> = li \<cdot> \<mu>" 
      proof (intro bexI[OF _  tl'] exI[of _ \<mu>], clarify)
        fix ti li
        assume tli: "(ti, li) \<in> tl'" 
        hence tlit: "(ti \<cdot> \<tau>, li) \<in> tl" unfolding tl by force
        from match[OF this] have match: "ti \<cdot> \<tau> \<cdot> \<sigma>' = li \<cdot> \<mu>" by auto
        from *(1)[unfolded tvars_disj_pp_def, rule_format, OF tl' tli]
        have vti: "fst ` vars_term ti \<inter> {n..<n + m} = {}" by auto
        have "ti \<cdot> \<sigma> = ti \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>')" 
        proof (rule term_subst_eq, unfold subst_compose_def)
          fix y
          assume "y \<in> vars_term ti" 
          with vti have y: "fst y \<notin> {n..<n + m}" by auto
          show "\<sigma> y = \<tau> y \<cdot> \<sigma>'" 
          proof (cases "y = x")
            case False
            hence "\<tau> y \<cdot> \<sigma>' = \<sigma>' y" unfolding \<tau>_def subst_def by auto
            also have "\<dots> = \<sigma> y" 
              unfolding \<sigma>'_def using y l by auto
            finally show ?thesis by simp
          next
            case True
            show ?thesis unfolding True \<tau>_def subst_simps \<sigma>x eval_term.simps map_map o_def term.simps
              by (intro conjI refl nth_equalityI, auto simp: len \<sigma>'_def)
          qed
        qed  
        also have "\<dots> = li \<cdot> \<mu>" using match by simp
        finally show "ti \<cdot> \<sigma> = li \<cdot> \<mu>" by blast
      qed
    qed
  next
    assume complete: "pat_complete C pp"
    show "\<forall>pp \<in> P'. pat_complete C pp"
      apply (unfold P'_def) 
    proof safe
      fix \<tau>
      assume "\<tau> \<in> \<tau>s n x"
      from this[unfolded \<tau>s_def \<tau>c_def, simplified]
      obtain f \<iota>s where f: "f : \<iota>s \<rightarrow> snd x in C" and \<tau>: "\<tau> = subst x (Fun f (map Var (zip [n..<n + length \<iota>s] \<iota>s)))" by auto
      let ?i = "length \<iota>s" 
      let ?xs = "zip [n..<n + length \<iota>s] \<iota>s"
      have i: "?i \<le> m" by (rule m[OF f])
      have "\<forall>\<iota> \<in> set \<iota>s. \<iota> \<in> S" using C_sub_S f by blast 
      with Fun_hastypeI[OF f, of "{x : \<iota> in \<V>. \<iota> \<in> S}" "map Var ?xs"] wfpp
      have "\<tau> :\<^sub>s \<V> |` tvars_pat pp \<rightarrow> \<T>(C,{x : \<iota> in \<V>. \<iota> \<in> S})"
        by (auto intro!: sorted_mapI
            simp: \<tau> subst_def hastype_restrict list_all2_conv_all_nth wf_pat_iff)
      note def2 = def[OF wf_pat_subst[OF this]]
      show "pat_complete C (subst_pat_problem_set \<tau> pp)" unfolding def2
      proof (intro allI impI)
        fix \<sigma> assume cg: "\<sigma> :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)"
        define \<sigma>' where "\<sigma>' = \<sigma>(x := Fun f (map \<sigma> ?xs))" 
        from C_sub_S[OF f] have sortsS: "set \<iota>s \<subseteq> S" by auto
        from f have f: "f : \<iota>s \<rightarrow> snd x in C" by (simp add: fun_hastype_def)
        with sorted_mapD[OF cg] set_mp[OF sortsS]
        have "Fun f (map \<sigma> ?xs) : snd x in \<T>(C)" 
          by (auto intro!: Fun_hastypeI simp: list_all2_conv_all_nth)
        with sorted_mapD[OF cg]
        have cg: "\<sigma>' :\<^sub>s {x : \<iota> in \<V>. \<iota> \<in> S} \<rightarrow> \<T>(C)" by (auto intro!: sorted_mapI simp: \<sigma>'_def)
        from complete[unfolded def[OF wfpp], rule_format, OF this] 
        obtain tl \<mu> where tl: "tl \<in> pp" and tli: "\<And> ti li. (ti, li)\<in> tl \<Longrightarrow> ti \<cdot> \<sigma>' = li \<cdot> \<mu>" by force
        from tl have tlm: "{(t \<cdot> \<tau>, l) |. (t,l) \<in> tl} \<in> subst_pat_problem_set \<tau> pp"
          unfolding subst_defs_set subst_left_def by auto
        {
          fix ti li
          assume mem: "(ti, li) \<in> tl"
          from *[unfolded tvars_disj_pp_def] tl mem have vti: "fst ` vars_term ti \<inter> {n..<n + m} = {}" by force
          from tli[OF mem] have "li \<cdot> \<mu> = ti \<cdot> \<sigma>'" by auto
          also have "\<dots> = ti \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)"
          proof (intro term_subst_eq, unfold subst_compose_def)
            fix y
            assume "y \<in> vars_term ti" 
            with vti have y: "fst y \<notin> {n..<n + m}" by auto
            show "\<sigma>' y = \<tau> y \<cdot> \<sigma>" 
            proof (cases "y = x")
              case False
              hence "\<tau> y \<cdot> \<sigma> = \<sigma> y" unfolding \<tau> subst_def by auto
              also have "\<dots> = \<sigma>' y" 
                unfolding \<sigma>'_def using False by auto
              finally show ?thesis by simp
            next
              case True
              show ?thesis unfolding True \<tau>
                by (simp add: o_def \<sigma>'_def)
            qed
          qed
          finally have "ti \<cdot> \<tau> \<cdot> \<sigma> = li \<cdot> \<mu>" by auto
        }
        thus "\<exists>tl \<in> subst_pat_problem_set \<tau> pp. \<exists>\<mu>. \<forall>(ti, li)\<in>tl. ti \<cdot> \<sigma> = li \<cdot> \<mu>" 
          by (intro bexI[OF _ tlm], auto)
      qed
    qed
  qed
qed 
end

text \<open>Represent a variable-form as a set of maps.\<close>

definition "match_of_var_form f = {(Var y, Var x) | x y. y \<in> f x}"

definition "pat_of_var_form ff = match_of_var_form ` ff"

definition "var_form_of_match mp x = {y. (Var y, Var x) \<in> mp}"

definition "var_form_of_pat pp = var_form_of_match ` pp"

definition "tvars_var_form_pat ff = (\<Union>f \<in> ff. \<Union>(range f))"

definition var_form_match where
  "var_form_match mp \<longleftrightarrow> mp \<subseteq> range (map_prod Var Var)"

definition "var_form_pat pp \<equiv> \<forall>mp \<in> pp. var_form_match mp"

lemma match_of_var_form_of_match:
  assumes "var_form_match mp"
  shows "match_of_var_form (var_form_of_match mp) = mp"
  using assms
  by (auto simp: var_form_match_def match_of_var_form_def var_form_of_match_def)

lemma tvars_match_var_form:
  assumes "var_form_match mp"
  shows "tvars_match mp = {v. \<exists>x. (Var v, Var x) \<in> mp}"
  using assms by (force simp: var_form_match_def tvars_match_def)

lemma pat_of_var_form_pat:
  assumes "var_form_pat pp"
  shows "pat_of_var_form (var_form_of_pat pp) = pp"
  using assms match_of_var_form_of_match
  by (auto simp: var_form_pat_def var_form_of_pat_def pat_of_var_form_def)

lemma tvars_pat_var_form: "tvars_pat (pat_of_var_form ff) = tvars_var_form_pat ff"
  by (fastforce simp: tvars_var_form_pat_def tvars_pat_def tvars_match_def pat_of_var_form_def match_of_var_form_def
      split: prod.splits)

lemma tvars_var_form_pat:
  assumes "var_form_pat pp"
  shows "tvars_var_form_pat (var_form_of_pat pp) = tvars_pat pp"
  apply (subst(2) pat_of_var_form_pat[OF assms,symmetric])
  by (simp add: tvars_pat_var_form)

lemma pat_complete_var_form:
  "pat_complete C (pat_of_var_form ff) \<longleftrightarrow>
  (\<forall>\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C). \<exists>f \<in> ff. \<exists>\<mu>. \<forall>x. \<forall>y \<in> f x. \<sigma> y = \<mu> x)"
proof-
  define V where "V = \<V> |` tvars_var_form_pat ff"
  have boo: "\<V> |` tvars_pat {{(Var (a, b), Var xa) | xa a b. (a, b) \<in> x xa} |. x \<in> ff} = V"
    apply (unfold V_def)
    apply (subst tvars_pat_var_form[of ff, symmetric])
    by (auto simp: V_def pat_of_var_form_def match_of_var_form_def)
  show ?thesis
    apply (fold V_def)
    apply (auto simp: pat_complete_def match_complete_wrt_def pat_of_var_form_def
      match_of_var_form_def imp_conjL imp_ex boo)
    apply (metis old.prod.exhaust)
    by metis
qed

lemma pat_complete_var_form_set:
  "pat_complete C (pat_of_var_form ff) \<longleftrightarrow>
  (\<forall>\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C). \<exists>f \<in> ff. \<exists>\<mu>. \<forall>x. \<sigma> ` f x \<subseteq> {\<mu> x})"
  by (auto simp: pat_complete_var_form image_subset_iff)

lemma pat_complete_var_form_Uniq:
  "pat_complete C (pat_of_var_form ff) \<longleftrightarrow>
  (\<forall>\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C). \<exists>f \<in> ff. \<forall>x. UNIQ (\<sigma> ` f x))"
proof-
  { fix \<sigma> f assume \<sigma>: "\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C)" and f: "f \<in> ff"
    have "(\<exists>\<mu>. \<forall>x. \<sigma> ` f x \<subseteq> {\<mu> x}) \<longleftrightarrow> (\<forall>x. \<exists>\<^sub>\<le>\<^sub>1 y. y \<in> \<sigma> ` f x)"
    proof (safe)
      fix \<mu> x
      assume "\<forall>x. \<sigma> ` f x \<subseteq> {\<mu> x}"
      from this[rule_format, of x]
      have "y \<in> f x \<Longrightarrow> \<sigma> y = \<mu> x" for y by auto
      then show "\<exists>\<^sub>\<le>\<^sub>1 y. y \<in> \<sigma> ` f x" by (auto intro!: Uniq_I)
    next
      define \<mu> where "\<mu> x = the_elem (\<sigma> ` f x)" for x
      fix x assume "\<forall>x. \<exists>\<^sub>\<le>\<^sub>1 y. y \<in> \<sigma> ` f x"
      from Uniq_eq_the_elem[OF this[rule_format], folded \<mu>_def]
      show "\<exists>\<mu>. \<forall>x. \<sigma> ` f x \<subseteq> {\<mu> x}" by auto
    qed
  }
  then show ?thesis by (simp add: pat_complete_var_form_set)
qed

lemma ex_var_form_pat: "(\<exists>f\<in>var_form_of_pat pp. P f) \<longleftrightarrow> (\<exists>mp \<in> pp. P (var_form_of_match mp))"
  by (auto simp: var_form_of_pat_def)

lemma pat_complete_var_form_nat:
  assumes fin: "\<forall>(x,\<iota>) \<in> tvars_var_form_pat ff. finite_sort C \<iota>"
    and uniq: "\<forall>f \<in> ff. \<forall>x::'v. UNIQ (snd ` f x)"
  shows "pat_complete C (pat_of_var_form ff) \<longleftrightarrow>
  (\<forall>\<alpha>. (\<forall>v \<in> tvars_var_form_pat ff. \<alpha> v < card_of_sort C (snd v)) \<longrightarrow>
  (\<exists>f \<in> ff. \<forall>x. UNIQ (\<alpha> ` f x)))"
  (is "?l \<longleftrightarrow> (\<forall>\<alpha>. ?s \<alpha> \<longrightarrow> ?r \<alpha>)")
proof safe
  note fin = fin[unfolded Ball_Pair_conv, rule_format]
  { fix \<alpha>
    assume l: ?l and a: "?s \<alpha>"
    define \<sigma> :: "_ \<Rightarrow> (_,unit) term" where
      "\<sigma> \<equiv> \<lambda>(x,\<iota>). term_of_index C \<iota> (\<alpha> (x,\<iota>))"
    have "\<sigma> (x,\<iota>) : \<iota> in \<T>(C)" if x: "(x,\<iota>) \<in> tvars_var_form_pat ff" for x \<iota>
      using term_of_index_bij[OF fin, OF x]
        a[unfolded Ball_Pair_conv, rule_format, OF x]
      by (auto simp: bij_betw_def \<sigma>_def)
    then have "\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C)"
      by (auto intro!: sorted_mapI simp: hastype_restrict)
    from l[unfolded pat_complete_var_form_Uniq, rule_format, OF this]
    obtain f where f: "f \<in> ff" and u: "\<And>x. UNIQ (\<sigma> ` f x)" by auto
    have id: "y \<in> f x \<Longrightarrow> index_of_term C (\<sigma> y) = \<alpha> y" for y x
      using assms a f
      by (force simp: \<sigma>_def index_of_term_of_index tvars_var_form_pat_def Ball_def split: prod.splits)
    then have "\<alpha> ` f x = index_of_term C ` \<sigma> ` f x" for x
      by (auto simp: image_def)
    then have "UNIQ (\<alpha> ` f x)" for x by (simp add: image_Uniq[OF u])
    with f show "?r \<alpha>" by auto
  next
    assume r: "\<forall>\<alpha>. ?s \<alpha> \<longrightarrow> ?r \<alpha>"
    show ?l
      unfolding pat_complete_var_form_Uniq
    proof safe
      fix \<sigma>
      assume \<sigma>: "\<sigma> :\<^sub>s \<V> |` tvars_var_form_pat ff \<rightarrow> \<T>(C)"
      from sorted_mapD[OF this]
      have ty: "(x,\<iota>) \<in> tvars_var_form_pat ff \<Longrightarrow> \<sigma> (x,\<iota>) : \<iota> in \<T>(C)"
        for x \<iota> by (auto simp: hastype_restrict)
      define \<alpha> where "\<alpha> \<equiv> index_of_term C \<circ> \<sigma>"
      have "\<alpha> (x,\<iota>) < card_of_sort C \<iota>" if x: "(x,\<iota>) \<in> tvars_var_form_pat ff"
        for x \<iota> using index_of_term_bij[OF fin[OF x]] ty[OF x]
        by (auto simp: \<alpha>_def bij_betw_def)
      then have "\<exists>f\<in>ff. \<forall>x. UNIQ (\<alpha> ` f x)" by (auto intro!: r[rule_format])
      then obtain f where f: "f \<in> ff" and u: "\<And>x. UNIQ (\<alpha> ` f x)" by auto
      have "UNIQ (\<sigma> ` f x)" for x
      proof-
        from uniq[rule_format, OF f]
        have ex: "\<exists>\<iota>. snd ` f x \<subseteq> {\<iota>}"
          by (auto simp: subset_singleton_iff_Uniq)
        then obtain \<iota> where sub: "snd ` f x \<subseteq> {\<iota>}" by auto
        { fix y \<kappa> assume yk: "(y,\<kappa>) \<in> f x"
          with sub have [simp]: "\<kappa> = \<iota>" by auto 
          from yk f have y: "(y,\<iota>) \<in> tvars_var_form_pat ff"
            by (auto simp: tvars_var_form_pat_def)
          from y fin[OF y]
          have "term_of_index C \<iota> (\<alpha> (y,\<kappa>)) = \<sigma> (y,\<kappa>)"
            by (auto simp: \<alpha>_def hastype_restrict
                intro!: term_of_index_of_term sorted_mapD[OF \<sigma>])
        }
        then have "y \<in> f x \<Longrightarrow> term_of_index C \<iota> (\<alpha> y) = \<sigma> y" for y
          by (cases y, auto)
        then have "\<sigma> ` f x = term_of_index C \<iota> ` \<alpha> ` f x"
          by (auto simp: image_def)
        then show "UNIQ (\<sigma> ` f x)" by (simp add: image_Uniq[OF u])
      qed
      with f show "\<exists>f \<in> ff. \<forall>x. UNIQ (\<sigma> ` f x)" by auto
    qed
  }
qed

text \<open>A problem is in finite variable form, if only variables occur in the problem and
   these variable all have a finite sort. Moreover, comparison of variables is only done
   if they have the same sort.
\<close>

definition finite_var_form_match :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "finite_var_form_match C mp \<longleftrightarrow> var_form_match mp \<and>
  (\<forall>l x y. (Var x, l) \<in> mp \<longrightarrow> (Var y, l) \<in> mp \<longrightarrow> snd x = snd y) \<and>
  (\<forall>l x. (Var x, l) \<in> mp \<longrightarrow> finite_sort C (snd x))"

lemma finite_var_form_matchD:
  assumes "finite_var_form_match C mp" and "(t,l) \<in> mp"
  shows "\<exists>x \<iota> y. t = Var (x,\<iota>) \<and> l = Var y \<and> finite_sort C \<iota> \<and>
    (\<forall>z. (Var z, Var y) \<in> mp \<longrightarrow> snd z = \<iota>)"
  using assms by (auto simp: finite_var_form_match_def var_form_match_def)

definition finite_var_form_pat :: "('f,'s) ssig \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "finite_var_form_pat C p = (\<forall> mp \<in> p. finite_var_form_match C mp)"

lemma finite_var_form_patD:
  assumes "finite_var_form_pat C pp" "mp \<in> pp" "(t,l) \<in> mp"
  shows "\<exists>x \<iota> y. t = Var (x,\<iota>) \<and> l = Var y \<and> finite_sort C \<iota> \<and>
    (\<forall>z. (Var z, Var y) \<in> mp \<longrightarrow> snd z = \<iota>)"
  using assms[unfolded finite_var_form_pat_def] finite_var_form_matchD by metis

lemma finite_var_form_imp_of_var_form_pat:
  "finite_var_form_pat C pp \<Longrightarrow> var_form_pat pp"
  by (auto simp: finite_var_form_pat_def var_form_pat_def finite_var_form_match_def)

context pattern_completeness_context begin

definition weak_finite_var_form_match :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "weak_finite_var_form_match mp = ((\<forall> (t,l) \<in> mp. \<exists> y. l = Var y)
     \<and> (\<forall> f ts y. (Fun f ts, Var y) \<in> mp \<longrightarrow>  
          (\<exists> x. (Var x, Var y) \<in> mp \<and> inf_sort (snd x))
        \<and> (\<forall> t. (t, Var y) \<in> mp \<longrightarrow> root t \<in> {None, Some (f,length ts)})))"

definition weak_finite_var_form_pat :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "weak_finite_var_form_pat p = (\<forall> mp \<in> p. weak_finite_var_form_match mp)"

end

lemma finite_var_form_pat_UNIQ_sort:
  assumes fvf: "finite_var_form_pat C pp"
    and f: "f \<in> var_form_of_pat pp"
  shows "UNIQ (snd ` f x)"
proof (intro Uniq_I, clarsimp)
  from f obtain mp where mp: "mp \<in> pp" and f: "f = var_form_of_match mp"
    by (auto simp: var_form_of_pat_def)
  fix y \<iota> z \<kappa> assume "(y,\<iota>) \<in> f x" "(z,\<kappa>) \<in> f x"
  with f have y: "(Var (y,\<iota>), Var x) \<in> mp" and z: "(Var (z,\<kappa>), Var x) \<in> mp"
    by (auto simp: var_form_of_match_def)
  from finite_var_form_patD[OF fvf mp y] z
  show "\<iota> = \<kappa>" by auto
qed

lemma finite_var_form_pat_pat_complete:
  assumes fvf: "finite_var_form_pat C pp"
  shows "pat_complete C pp \<longleftrightarrow>
    (\<forall>\<alpha>. (\<forall>v \<in> tvars_pat pp. \<alpha> v < card_of_sort C (snd v)) \<longrightarrow>
    (\<exists>mp \<in> pp. \<forall>x. UNIQ {\<alpha> y |y. (Var y, Var x) \<in> mp}))"
proof-
  note vf = finite_var_form_imp_of_var_form_pat[OF fvf]
  note pat_complete_var_form_nat[of "var_form_of_pat pp" C]
  note this[unfolded tvars_var_form_pat[OF vf]]
  note * = this[unfolded pat_of_var_form_pat[OF vf]]
  show ?thesis
    apply (subst *)
    subgoal
    proof
      fix y \<iota>
      assume y: "(y,\<iota>) \<in> tvars_pat pp"
      from y obtain mp t l where mp: "mp \<in> pp" and tl:"(t,l) \<in> mp" and yt: "(y, \<iota>) \<in> vars t"
        by (auto simp: tvars_pat_def tvars_match_def)
      from finite_var_form_patD[OF fvf mp tl] yt
      show "finite_sort C \<iota>" by auto
    qed
    subgoal using finite_var_form_pat_UNIQ_sort[OF fvf] by force
    subgoal 
      apply (rule all_cong)
      apply (unfold ex_var_form_pat)
      apply (rule bex_cong[OF refl])
      apply (rule all_cong1)
      apply (rule arg_cong[of _ _ UNIQ])
      by (auto simp: var_form_of_match_def)
    done
qed

end
