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
    Sorted_Terms.Sorted_Contexts
begin

subsection \<open>Definition of Algorithm -- Inference Rules\<close>

text \<open>We first consider matching problems which are sets of term pairs.
  Note that in the term pairs the type of variables differ: 
  Each left term has natural numbers (with sorts) as variables, 
  so that it is easy to generate new variables,
  whereas each right term has arbitrary variables of type \<open>'v\<close> without any further information.
  Then pattern problems are sets of matching problems, and we also have sets of pattern problems.

  The suffix \<open>_set\<close> is used to indicate that here these problems are modeled via sets.\<close>

type_synonym ('f,'v,'s)match_problem_set = "(('f,nat \<times> 's)term \<times> ('f,'v)term) set" 
type_synonym ('f,'v,'s)pat_problem_set = "('f,'v,'s)match_problem_set set" 
type_synonym ('f,'v,'s)pats_problem_set = "('f,'v,'s)pat_problem_set set" 

abbreviation (input) bottom :: "('f,'v,'s)pats_problem_set" where "bottom \<equiv> {{}}"

definition subst_left :: "('f,nat \<times> 's)subst \<Rightarrow> (('f,nat \<times> 's)term \<times> ('f,'v)term) \<Rightarrow> (('f,nat \<times> 's)term \<times> ('f,'v)term)" where
  "subst_left \<tau> = (\<lambda>(t,r). (t \<cdot> \<tau>, r))"

text \<open>A function to compute for a variable $x$ all substitution that instantiate
  $x$ by $c(x_n, ..., x_{n+a})$ where $c$ is an constructor of arity $a$ and $n$ is a parameter that
  determines from where to start the numbering of variables.\<close>

definition \<tau>c :: "nat \<Rightarrow> nat \<times> 's \<Rightarrow> 'f \<times> 's list \<Rightarrow> ('f,nat \<times> 's)subst" where 
  "\<tau>c n x = (\<lambda>(f,ss). subst x (Fun f (map Var (zip [n ..< n + length ss] ss))))"

text \<open>Compute the list of conflicting variables (Some list), or detect a clash (None)\<close>
fun conflicts :: "('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> 'v list option" where 
  "conflicts (Var x) (Var y) = (if x = y then Some [] else Some [x,y])" 
| "conflicts (Var x) (Fun _ _) = (Some [x])"
| "conflicts (Fun _ _) (Var x) = (Some [x])" 
| "conflicts (Fun f ss) (Fun g ts) = (if (f,length ss) = (g,length ts)
     then map_option concat (those (map2 conflicts ss ts))
    else None)" 
          
abbreviation "Conflict_Var s t x \<equiv> conflicts s t \<noteq> None \<and> x \<in> set (the (conflicts s t))" 
abbreviation "Conflict_Clash s t \<equiv> conflicts s t = None" 

locale pattern_completeness_context =
  fixes S :: "'s set" \<comment> \<open>set of sort-names\<close>
    and C :: "('f,'s)ssig" \<comment> \<open>sorted signature\<close>
    and m :: nat \<comment> \<open>upper bound on arities of constructors\<close>
    and Cl :: "'s \<Rightarrow> ('f \<times> 's list)list" \<comment> \<open>a function to compute all constructors of given sort as list\<close> 
    and inf_sort :: "'s \<Rightarrow> bool" \<comment> \<open>a function to indicate whether a sort is infinite\<close>
    and ty :: "'v itself" \<comment> \<open>fix the type-variable for term-variables\<close>
begin

definition tvars_disj_pp :: "nat set \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "tvars_disj_pp V p = (\<forall> mp \<in> p. \<forall> (ti,pi) \<in> mp. fst ` vars ti \<inter> V = {})" 

definition lvars_disj_mp :: "'v list \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "lvars_disj_mp ys mp = (\<Union> (vars ` snd ` mp) \<inter> set ys = {} \<and> distinct ys)" 

definition inf_var_conflict :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "inf_var_conflict mp = (\<exists> s t x y. 
    (s,Var x) \<in> mp \<and> (t,Var x) \<in> mp \<and> Conflict_Var s t y \<and> inf_sort (snd y))" 

definition tvars_mp :: "('f,'v,'s)match_problem_set \<Rightarrow> (nat \<times> 's) set" where
  "tvars_mp mp = (\<Union>(t,l) \<in> mp. vars t)"

definition tvars_pp :: "('f,'v,'s)pat_problem_set \<Rightarrow> (nat \<times> 's) set" where
  "tvars_pp pp = (\<Union>mp \<in> pp. tvars_mp mp)"

definition subst_match_problem_set :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> ('f,'v,'s)match_problem_set" where
  "subst_match_problem_set \<tau> pp = subst_left \<tau> ` pp" 

definition subst_pat_problem_set :: "('f,nat \<times> 's)subst \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> ('f,'v,'s)pat_problem_set" where
  "subst_pat_problem_set \<tau> P = subst_match_problem_set \<tau> ` P"

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

inductive mp_fail :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  mp_clash: "(f,length ts) \<noteq> (g,length ls) \<Longrightarrow> mp_fail (insert (Fun f ts, Fun g ls) mp)" 
| mp_clash': "Conflict_Clash s t \<Longrightarrow> mp_fail ({(s,Var x),(t, Var x)} \<union> mp)"

inductive pp_step :: "('f,'v,'s)pat_problem_set \<Rightarrow> ('f,'v,'s)pat_problem_set \<Rightarrow> bool"
(infix \<open>\<Rightarrow>\<^sub>s\<close> 50) where
  pp_simp_mp: "mp \<rightarrow>\<^sub>s mp' \<Longrightarrow> insert mp pp \<Rightarrow>\<^sub>s insert mp' pp" 
| pp_remove_mp: "mp_fail mp \<Longrightarrow> insert mp pp \<Rightarrow>\<^sub>s pp"

inductive pp_success :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "pp_success (insert {} pp)" 

inductive P_step_set :: "('f,'v,'s)pats_problem_set \<Rightarrow> ('f,'v,'s)pats_problem_set \<Rightarrow> bool"
(infix \<open>\<Rrightarrow>\<^sub>s\<close> 50) where
  P_fail: "insert {} P \<Rrightarrow>\<^sub>s bottom"
| P_simp: "pp \<Rightarrow>\<^sub>s pp' \<Longrightarrow> insert pp P \<Rrightarrow>\<^sub>s insert pp' P"
| P_remove_pp: "pp_success pp \<Longrightarrow> insert pp P \<Rrightarrow>\<^sub>s P"
| P_instantiate: "tvars_disj_pp {n ..< n+m} pp \<Longrightarrow> x \<in> tvars_pp pp \<Longrightarrow>
    insert pp P \<Rrightarrow>\<^sub>s {subst_pat_problem_set \<tau> pp |. \<tau> \<in> \<tau>s n x} \<union> P"
| P_failure': "\<forall>mp \<in> pp. inf_var_conflict mp \<Longrightarrow> finite pp \<Longrightarrow> insert pp P \<Rrightarrow>\<^sub>s {{}}"

text \<open>Note that in @{thm[source] P_failure'} the conflicts have to be simultaneously occurring. 
  If just some matching problem has such a conflict, then this cannot be deleted immediately!

  Example-program: f(x,x) = ..., f(s(x),y) = ..., f(x,s(y)) = ... cover all cases of natural numbers,
    i.e., f(x1,x2), but if one would immediately delete the matching problem of the first lhs
    because of the resulting @{const inf_var_conflict} in {(x1,x),(x2,x)} then it is no longer complete.\<close>



subsection \<open>Soundness of the inference rules\<close>


text \<open>The empty set of variables\<close>
definition EMPTY :: "'v \<Rightarrow> 's option" where "EMPTY x = None" 
definition EMPTYn :: "nat \<times> 's \<Rightarrow> 's option" where "EMPTYn x = None" 

text \<open>A constructor-ground substitution for the fixed set of constructors and set of sorts. 
  Note that variables to instantiate are represented as pairs of (number, sort).\<close>
definition cg_subst :: "('f,nat \<times> 's,'v)gsubst \<Rightarrow> bool" where
  "cg_subst \<sigma> = (\<forall> x. snd x \<in> S \<longrightarrow> (\<sigma> x : snd x in \<T>(C,EMPTY)))" 

text \<open>A definition of pattern completeness for pattern problems.\<close>

definition match_complete_wrt :: "('f,nat \<times> 's,'v)gsubst \<Rightarrow> ('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "match_complete_wrt \<sigma> mp = (\<exists> \<mu>. \<forall> (t,l) \<in> mp. t \<cdot> \<sigma> = l \<cdot> \<mu>)" 

definition pat_complete :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "pat_complete pp = (\<forall>\<sigma>. cg_subst \<sigma> \<longrightarrow> (\<exists> mp \<in> pp. match_complete_wrt \<sigma> mp))"

abbreviation "pats_complete P \<equiv> \<forall>pp \<in> P. pat_complete pp"

text \<open>Well-formed matching and pattern problems: all occurring variables 
  (in left-hand sides of matching problems) have a known sort.\<close>
definition wf_match :: "('f,'v,'s)match_problem_set \<Rightarrow> bool" where
  "wf_match mp = (snd ` tvars_mp mp \<subseteq> S)" 

definition wf_pat :: "('f,'v,'s)pat_problem_set \<Rightarrow> bool" where
  "wf_pat pp = (\<forall>mp \<in> pp. wf_match mp)" 

definition wf_pats :: "('f,'v,'s)pats_problem_set \<Rightarrow> bool" where
  "wf_pats P = (\<forall>pp \<in> P. wf_pat pp)" 
end

lemma type_conversion: "t : s in \<T>(C,\<emptyset>) \<Longrightarrow> t \<cdot> \<sigma> : s in \<T>(C,\<emptyset>)" 
proof (induct t s rule: hastype_in_Term_induct)
  case (Fun f ss \<sigma>s \<tau>)
  then show ?case unfolding eval_term.simps
    by (smt (verit, best) Fun_hastype list_all2_map1 list_all2_mono)
qed auto

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


lemma conflicts: fixes x :: 'v
  shows "Conflict_Clash s t \<Longrightarrow> \<exists> p. p \<in> poss s \<and> p \<in> poss t \<and> is_Fun (s |_p) \<and> is_Fun (t |_p) \<and> root (s |_p) \<noteq> root (t |_ p)" (is "?B1 \<Longrightarrow> ?B2")
    and "Conflict_Var s t x \<Longrightarrow>
         \<exists> p . p \<in> poss s \<and> p \<in> poss t \<and> s |_p \<noteq> t |_p \<and> (s |_p = Var x \<or> t |_p = Var x)" (is "?C1 x \<Longrightarrow> ?C2 x")
    and "s \<noteq> t \<Longrightarrow> \<exists> x. Conflict_Clash s t \<or> Conflict_Var s t x" 
    and "Conflict_Var s t x \<Longrightarrow> x \<in> vars s \<union> vars t" 
    and "conflicts s t = Some [] \<longleftrightarrow> s = t" (is ?A)
proof -
  let ?B = "?B1 \<longrightarrow> ?B2" 
  let ?C = "\<lambda> x. ?C1 x \<longrightarrow> ?C2 x" 
  {
    fix x :: 'v
    have "(conflicts s t = Some [] \<longrightarrow> s = t) \<and> ?B \<and> ?C x"
    proof (induction s arbitrary: t)
      case (Var y t)
      thus ?case by (cases t, auto)
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
              where p: "p \<in> poss (ss ! i) \<and> p \<in> poss (ts ! i) \<and> is_Fun (ss ! i |_ p) \<and> is_Fun (ts ! i |_ p) \<and> root (ss ! i |_ p) \<noteq> root (ts ! i |_ p)" 
              by auto
            from p have p: "\<exists> p. p \<in> poss ?s \<and> p \<in> poss t \<and> is_Fun (?s |_ p) \<and> is_Fun (t |_ p) \<and> root (?s |_ p) \<noteq> root (t |_ p)" 
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
    with B have "conflicts s t \<noteq> None" by blast
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
      thus ?thesis unfolding Some by auto
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


text \<open>For proving partial correctness we need further properties of the fixed parameters:
   We assume that \<open>m\<close> is sufficiently large and that there exists some constructor ground terms.
   Moreover \<open>inf_sort\<close> really computes whether a sort has terms of arbitrary size.
   Further all symbols in \<open>C\<close> must have sorts of \<open>S\<close>.
   Finally, \<open>Cl\<close> should precisely compute the constructors of a sort.\<close>

locale pattern_completeness_context_with_assms = pattern_completeness_context S C m Cl inf_sort ty
  for S and C :: "('f,'s)ssig" 
    and m Cl inf_sort  
    and ty :: "'v itself" +
  assumes sorts_non_empty: "\<And> s. s \<in> S \<Longrightarrow> \<exists> t. t : s in \<T>(C, EMPTY)"  
    and C_sub_S: "\<And> f ss s. f : ss \<rightarrow> s in C \<Longrightarrow> insert s (set ss) \<subseteq> S" 
    and m: "\<And> f ss s. f : ss \<rightarrow> s in C \<Longrightarrow> length ss \<le> m"
    and inf_sort_def: "s \<in> S \<Longrightarrow> inf_sort s  = (\<not> bdd_above (size ` {t . t : s in \<T>(C,EMPTYn)}))" 
    and Cl: "\<And> s. set (Cl s) = {(f,ss). f : ss \<rightarrow> s in C}" 
    and Cl_len: "\<And> \<sigma>. Ball (length ` snd ` set (Cl \<sigma>)) (\<lambda> a. a \<le> m)" 
begin


lemmas subst_defs_set = 
  subst_pat_problem_set_def
  subst_match_problem_set_def

text \<open>Preservation of well-formedness\<close>

lemma mp_step_wf: "mp \<rightarrow>\<^sub>s mp' \<Longrightarrow> wf_match mp \<Longrightarrow> wf_match mp'" 
  unfolding wf_match_def tvars_mp_def
proof (induct mp mp' rule: mp_step.induct)
  case (mp_decompose f ts ls mp)
  then show ?case by (auto dest!: set_zip_leftD)
next 
  case *: (mp_decompose' mp y f n mp' ys)
  from *(1) *(5)  
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
  from * have sS: "?s \<in> S" and p: "wf_pat p" unfolding wf_pat_def wf_match_def tvars_pp_def by auto
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
      assume mp: "mp \<in> p"  and "y \<in> tvars_mp (subst_left \<tau> ` mp)"
      then obtain s t where y: "y \<in> vars (s \<cdot> \<tau>)" and st: "(s,t) \<in> mp" 
        unfolding tvars_mp_def subst_left_def by auto
      from y have "y \<in> vars s \<union> set ?xs" unfolding vars_term_subst \<tau>
        by (auto simp: subst_def split: if_splits)
      hence "snd y \<in> snd ` vars s \<union> snd ` set ?xs" by auto
      also have "\<dots> \<subseteq> snd ` vars s \<union> S" using xs by auto
      also have "\<dots> \<subseteq> S" using p mp st
        unfolding wf_pat_def wf_match_def tvars_mp_def by force
      finally have "snd y \<in> S" .
    }
    hence "wf_pat (subst_pat_problem_set \<tau> p)" 
      unfolding wf_pat_def wf_match_def subst_defs_set by auto
  }
  with * show ?case by auto
qed (auto simp: wf_pat_def)


text \<open>Soundness requires some preparations\<close>


lemma cg_exists: "\<exists> \<sigma>g. cg_subst \<sigma>g" 
proof
  show "cg_subst (\<lambda> x. SOME t. t : snd x in \<T>(C, EMPTY))" 
    unfolding cg_subst_def
  proof (intro allI impI, goal_cases)
    case (1 x)
    from someI_ex[OF sorts_non_empty[OF 1]] show ?case by simp
  qed
qed
 
definition \<sigma>g :: "('f,nat \<times> 's,'v)gsubst" where "\<sigma>g = (SOME \<sigma>. cg_subst \<sigma>)" 

lemma \<sigma>g: "cg_subst \<sigma>g" unfolding \<sigma>g_def using cg_exists by (metis someI_ex)

lemma pat_complete_empty[simp]: "pat_complete {} = False" 
  unfolding pat_complete_def using \<sigma>g by auto

lemma inf_var_conflictD: assumes "inf_var_conflict mp" 
  shows "\<exists> p s t x y. 
    (s,Var x) \<in> mp \<and> (t,Var x) \<in> mp \<and> s |_p = Var y \<and> s |_ p \<noteq> t |_p  \<and> p \<in> poss s \<and> p \<in> poss t \<and> inf_sort (snd y)" 
proof -
  from assms[unfolded inf_var_conflict_def]
  obtain s t x y where "(s, Var x) \<in> mp \<and> (t, Var x) \<in> mp" and conf: "Conflict_Var s t y" and y: "inf_sort (snd y)" by blast
  with conflicts(2)[OF conf] show ?thesis by metis
qed

lemma cg_term_vars: "t : s in \<T>(C,EMPTYn) \<Longrightarrow> vars t = {}" 
proof (induct t s rule: hastype_in_Term_induct)
  case (Var v \<sigma>)
  then show ?case by (auto simp: EMPTYn_def)
next
  case (Fun f ss \<sigma>s \<tau>)
  then show ?case unfolding term.simps unfolding set_conv_nth list_all2_conv_all_nth by auto
qed

lemma type_conversion1: "t : s in \<T>(C,EMPTYn) \<Longrightarrow> t \<cdot> \<sigma>' : s in \<T>(C,EMPTY)" 
  unfolding EMPTYn_def EMPTY_def by (rule type_conversion)

lemma type_conversion2: "t : s in \<T>(C,EMPTY) \<Longrightarrow> t \<cdot> \<sigma>' : s in \<T>(C,EMPTYn)" 
  unfolding EMPTYn_def EMPTY_def by (rule type_conversion)

lemma term_of_sort: assumes "s \<in> S"
  shows "\<exists> t. t : s in \<T>(C,EMPTYn)" 
proof -
  from \<sigma>g[unfolded cg_subst_def] assms
  have "\<exists> t. t : s in \<T>(C,EMPTY)" by force
  with type_conversion2[of _ s]
  show ?thesis by auto
qed


text \<open>Main partial correctness theorems on well-formed problems: the transformation rules do
  not change the semantics of a problem\<close>

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

lemma mp_fail_pcorrect: "mp_fail mp \<Longrightarrow> \<not> match_complete_wrt \<sigma> mp" 
proof (induct mp rule: mp_fail.induct)
  case *: (mp_clash f ts g ls mp)
  {
    assume "length ts \<noteq> length ls" 
    hence "(map (\<lambda>t. t \<cdot> \<mu>) ls = map (\<lambda>t. t \<cdot> \<sigma>) ts) = False" for \<sigma> :: "('f,nat \<times> 's,'a)gsubst" and \<mu>
      by (metis length_map)
  } note len = this
  from * show ?case unfolding match_complete_wrt_def 
    by (auto simp: len) 
next
  case *: (mp_clash' s t x mp)
  from conflicts(1)[OF *(1)]
  obtain po where *: "po \<in> poss s" "po \<in> poss t" "is_Fun (s |_ po)" "is_Fun (t |_ po)" "root (s |_ po) \<noteq> root (t |_ po)" 
    by auto
  show ?case 
  proof 
    assume "match_complete_wrt \<sigma> ({(s, Var x), (t, Var x)} \<union> mp)" 
    from this[unfolded match_complete_wrt_def]
    have "s \<cdot> \<sigma> = t \<cdot> \<sigma>" by auto
    hence "root (s \<cdot> \<sigma> |_po) = root (t \<cdot> \<sigma> |_po)" by auto
    also have "root (s \<cdot> \<sigma> |_po) = root (s |_po \<cdot> \<sigma>)" using * by auto
    also have "\<dots> = root (s |_po)" using * by (cases "s |_ po", auto)
    also have "root (t \<cdot> \<sigma> |_po) = root (t |_po \<cdot> \<sigma>)" using * by (cases "t |_ po", auto)
    also have "\<dots> = root (t |_po)" using * by (cases "t |_ po", auto)
    finally show False using * by auto
  qed
qed

lemma pp_step_pcorrect: "pp \<Rightarrow>\<^sub>s pp' \<Longrightarrow> pat_complete pp = pat_complete pp'" 
proof (induct pp pp' rule: pp_step.induct)
  case (pp_simp_mp mp mp' pp)
  then show ?case using mp_step_pcorrect[of mp mp'] unfolding pat_complete_def by auto
next
  case (pp_remove_mp mp pp)
  then show ?case using mp_fail_pcorrect[of mp] unfolding pat_complete_def by auto
qed

lemma pp_success_pcorrect: "pp_success pp \<Longrightarrow> pat_complete pp" 
  by (induct pp rule: pp_success.induct, auto simp: pat_complete_def match_complete_wrt_def)



theorem P_step_set_pcorrect: "P \<Rrightarrow>\<^sub>s P' \<Longrightarrow> wf_pats P \<Longrightarrow>
  pats_complete P \<longleftrightarrow> pats_complete P'"
proof (induct P P' rule: P_step_set.induct)
  case (P_fail P)
  then show ?case by (auto simp: pat_complete_def)
next
  case (P_simp pp pp' P)
  then show ?case using pp_step_pcorrect[of pp pp'] by auto
next
  case (P_remove_pp pp P)
  then show ?case using pp_success_pcorrect[of pp] by auto
next
  case *: (P_instantiate n pp x P)
  note def = pat_complete_def[unfolded match_complete_wrt_def]
  show ?case
  proof (rule ball_insert_un_cong, standard)
    assume complete: "pats_complete {subst_pat_problem_set \<tau> pp |. \<tau> \<in> \<tau>s n x}" 
    show "pat_complete pp" unfolding def
    proof (intro allI impI)
      fix \<sigma> :: "('f,nat \<times> 's,'v)gsubst" 
      (* This is the step where well-formedness is essential *)
      from * have "wf_pat pp" unfolding wf_pats_def by auto
      with *(2) have x: "snd x \<in> S" unfolding tvars_pp_def tvars_mp_def wf_pat_def wf_match_def by force

      assume cg: "cg_subst \<sigma>" 
      from this[unfolded cg_subst_def] x 
      have "\<sigma> x : snd x in \<T>(C,EMPTY)" by blast
      then obtain f ts \<sigma>s where f: "f : \<sigma>s \<rightarrow> snd x in C" 
        and args: "ts :\<^sub>l \<sigma>s in \<T>(C,EMPTY)" 
        and \<sigma>x: "\<sigma> x = Fun f ts" 
        by (induct, auto simp: EMPTY_def)
      from f have f: "f : \<sigma>s \<rightarrow> snd x in C" 
        by (meson fun_hastype_def)
      let ?l = "length ts" 
      from args have len: "length \<sigma>s = ?l"
        by (simp add: list_all2_lengthD)
      have l: "?l \<le> m" using m[OF f] len by auto
      define \<sigma>' where "\<sigma>' = (\<lambda> ys. let y = fst ys in if n \<le> y \<and> y < n + ?l \<and> \<sigma>s ! (y - n) = snd ys then ts ! (y - n) else \<sigma> ys)" 
      have cg: "cg_subst \<sigma>'" unfolding cg_subst_def 
      proof (intro allI impI)
        fix ys :: "nat \<times> 's" 
        assume ysS: "snd ys \<in> S" 
        show "\<sigma>' ys : snd ys in \<T>(C,EMPTY)" 
        proof (cases "\<sigma>' ys = \<sigma> ys")
          case True
          thus ?thesis using cg ysS unfolding cg_subst_def by metis
        next
          case False
          obtain y s where ys: "ys = (y,s)" by force
          with False have y: "y - n < ?l" "n \<le> y" "y < n + ?l" and arg: "\<sigma>s ! (y - n) = s" and \<sigma>': "\<sigma>' ys = ts ! (y - n)" 
            unfolding \<sigma>'_def Let_def by (auto split: if_splits)
          show ?thesis unfolding \<sigma>' unfolding ys snd_conv arg[symmetric] using y(1) len args 
            by (metis list_all2_nthD)
        qed
      qed
      define \<tau> where "\<tau> = subst x (Fun f (map Var (zip [n..<n + ?l] \<sigma>s)))" 
      from f have "\<tau> \<in> \<tau>s n x" unfolding \<tau>s_def \<tau>_def \<tau>c_def using len[symmetric] by auto
      hence "pat_complete (subst_pat_problem_set \<tau> pp)" using complete by auto
      from this[unfolded def, rule_format, OF cg]
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
    assume complete: "pat_complete pp" 
    {
      fix \<tau>
      assume "\<tau> \<in> \<tau>s n x"
      from this[unfolded \<tau>s_def \<tau>c_def, simplified]
      obtain f sorts where f: "f : sorts \<rightarrow> snd x in C" and \<tau>: "\<tau> = subst x (Fun f (map Var (zip [n..<n + length sorts] sorts)))" by auto
      let ?i = "length sorts" 
      let ?xs = "zip [n..<n + length sorts] sorts" 
      have i: "?i \<le> m" by (rule m[OF f])
      have "pat_complete (subst_pat_problem_set \<tau> pp)" unfolding def
      proof (intro allI impI)
        fix \<sigma> :: "('f,nat \<times> 's,'v)gsubst" 
        assume cg: "cg_subst \<sigma>"
        define \<sigma>' where "\<sigma>' = \<sigma>(x := Fun f (map \<sigma> ?xs))" 
        from C_sub_S[OF f] have sortsS: "set sorts \<subseteq> S" by auto
        from f have f: "f : sorts \<rightarrow> snd x in C" by (simp add: fun_hastype_def)
        hence "Fun f (map \<sigma> ?xs) : snd x in \<T>(C,EMPTY)" 
        proof (rule Fun_hastypeI)
          show "map \<sigma> ?xs :\<^sub>l sorts in \<T>(C,EMPTY)" 
            using cg[unfolded cg_subst_def, rule_format, OF set_mp[OF sortsS]]
            by (smt (verit) add_diff_cancel_left' length_map length_upt length_zip list_all2_conv_all_nth min.idem nth_map nth_mem nth_zip prod.sel(2))
        qed
        hence cg: "cg_subst \<sigma>'" using cg f unfolding cg_subst_def \<sigma>'_def by auto
        from complete[unfolded def, rule_format, OF this] 
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
            with vti have y: "fst y \<notin>  {n..<n + m}" by auto
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
    }
    thus "pats_complete {subst_pat_problem_set \<tau> pp |. \<tau> \<in> \<tau>s n x}"  by auto
  qed
next
  case *: (P_failure' pp P)
  {  
    assume pp: "pat_complete pp" 
    with *(3) have wf: "wf_pat pp" by (auto simp: wf_pats_def)
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
            \<and> (\<not> var_ind i x \<longrightarrow> (vars_term (\<sigma> x) = {} \<and> (snd x \<in> S \<longrightarrow> \<sigma> x : snd x in \<T>(C,EMPTYn)))))" for i \<sigma>
    define confl :: "nat \<Rightarrow> ('f, nat \<times> 's) term \<Rightarrow> ('f, nat \<times> 's)term \<Rightarrow> bool" where "confl = (\<lambda> i sp tp. 
           (case (sp,tp) of (Var x, Var y) \<Rightarrow> x \<noteq> y \<and> var_ind i x \<and> var_ind i y
           | (Var x, Fun _ _) \<Rightarrow> var_ind i x
           | (Fun _ _, Var x) \<Rightarrow> var_ind i x
           | (Fun f ss, Fun g ts) \<Rightarrow> (f,length ss) \<noteq> (g,length ts)))"
    have confl_n: "confl n s t \<Longrightarrow> \<exists> f g ss ts. s = Fun f ss \<and> t = Fun g ts \<and> (f,length ss) \<noteq> (g,length ts)" for s t
      by (cases s; cases t; auto simp: confl_def)
    {
      fix i
      assume "i \<le> n"
      hence "\<exists> \<sigma>. cg_subst_ind i \<sigma> \<and> (\<forall> mp \<in> pp. \<exists> p. p \<in> poss (s mp \<cdot> \<sigma>) \<and> p \<in> poss (t mp \<cdot> \<sigma>) \<and> confl i (s mp \<cdot> \<sigma> |_ p) (t mp \<cdot> \<sigma> |_ p))" 
      proof (induction i)
        case 0
        define \<sigma> where "\<sigma> x = (if var_ind 0 x then Var x else if snd x \<in> S then map_vars undefined (\<sigma>g x) else Fun undefined [])" for x
        {
          fix x :: "nat \<times> 's" 
          define t where "t = \<sigma>g x"
          define s where "s = snd x" 
          assume "snd x \<in> S" 
          hence "\<sigma>g x : snd x in \<T>(C,EMPTY)" using \<sigma>g unfolding cg_subst_def by blast
          hence "map_vars undefined (\<sigma>g x) : snd x in \<T>(C,EMPTYn)" (is "?m : _ in _")
            unfolding t_def[symmetric] s_def[symmetric]
          proof (induct t s rule: hastype_in_Term_induct)
            case (Var v \<sigma>)
            then show ?case by (auto simp: EMPTY_def)
          next
            case (Fun f ss \<sigma>s \<tau>)
            then show ?case unfolding term.simps
              by (smt (verit, best) Fun_hastype list_all2_map1 list_all2_mono)
          qed
        }  
        from this cg_term_vars[OF this] have \<sigma>: "cg_subst_ind 0 \<sigma>" unfolding cg_subst_ind_def \<sigma>_def by auto
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
              with ssig[unfolded \<sigma>_def] have uS: "snd u \<in> S" and contra: "map_vars undefined (\<sigma>g u) = Var z" 
                by (auto split: if_splits)
              from \<sigma>g[unfolded cg_subst_def, rule_format, OF uS] contra
              have False by (cases "\<sigma>g u", auto simp: EMPTY_def)
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
          with *(3) have "z \<in> tvars_mp mp" unfolding tvars_mp_def by force
          with \<open>mp \<in> pp\<close> wf have "snd z \<in> S" unfolding wf_pat_def wf_match_def by auto
          from not_bdd_above_natD[OF inf[unfolded inf_sort_def[OF this]]] term_of_sort[OF this]
          have "\<And> n. \<exists> t. t : snd z in \<T>(C,EMPTYn) \<and> n < size t" by auto
        } note z_inf = this
        (* define d as 1 + maximal size of all s- and t-terms in pp \<sigma> *)
        define all_st where "all_st = (\<lambda> mp. s mp \<cdot> \<sigma>) ` pp \<union> (\<lambda> mp. t mp \<cdot> \<sigma>) ` pp" 
        have fin_all_st: "finite all_st" unfolding all_st_def using *(2) by simp
        define d :: nat where "d = Suc (Max (size ` all_st))" 
        from z_inf[of d]
        obtain u where u: "u : snd z in \<T>(C,EMPTYn)" and du: "d \<le> size u" by auto
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
          thus "\<sigma>' x : snd x in \<T>(C,EMPTYn)" 
            using \<sigma>[unfolded cg_subst_ind_def, rule_format, of x] u
            unfolding \<sigma>'_def var_ind_conv by auto
        next
          fix x
          assume "\<not> var_ind (Suc i) x"  
          hence "x = z \<or> \<not> var_ind i x" unfolding var_ind_conv by auto
          thus "vars (\<sigma>' x) = {}" unfolding \<sigma>'_upd using \<sigma>[unfolded cg_subst_ind_def, rule_format, of x] vars_u by auto
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
    define \<sigma>' :: "('f,nat \<times> 's,'v)gsubst" where "\<sigma>' x = Var undefined" for x
    let ?\<sigma> = "\<sigma> \<circ>\<^sub>s \<sigma>'" 
    have "cg_subst ?\<sigma>" unfolding cg_subst_def subst_compose_def
    proof (intro allI impI)
      fix x :: "nat \<times> 's" 
      assume "snd x \<in> S" 
      with \<sigma>[unfolded cg_subst_ind_def, rule_format, of x]
      have "\<sigma> x : snd x in \<T>(C,EMPTYn)" by auto
      thus "\<sigma> x \<cdot> \<sigma>' : snd x in \<T>(C,EMPTY)" by (rule type_conversion1)
    qed  
    from pp[unfolded pat_complete_def match_complete_wrt_def, rule_format, OF this]
    obtain mp \<mu> where mp: "mp \<in> pp" and match: "\<And> ti li. (ti, li)\<in> mp \<Longrightarrow> ti \<cdot> ?\<sigma> = li \<cdot> \<mu>" by force 
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
  thus ?case by auto
qed 
end
end
