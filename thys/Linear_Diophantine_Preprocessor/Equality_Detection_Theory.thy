section \<open>Detection of Implicit Equalities\<close>

subsection \<open>Main Abstract Reasoning Step\<close>

text \<open>The abstract reasoning steps is due to Bromberger and Weidenbach.
  Make all inequalities strict and detect a minimal unsat core; all inequalities
  in this core are implied equalities.\<close>

theory Equality_Detection_Theory
  imports 
    Farkas.Farkas
    Jordan_Normal_Form.Matrix
begin

lemma lec_rel_sum_list: "lec_rel (sum_list cs) = 
  (if (\<exists> c \<in> set cs. lec_rel c = Lt_Rel) then Lt_Rel else Leq_Rel)" 
proof (induct cs)
  case Nil
  thus ?case by (auto simp: zero_le_constraint_def)
next
  case (Cons c cs)
  thus ?case by (cases "sum_list cs"; cases c; cases "lec_rel c"; auto)
qed


lemma equality_detection_rat: fixes cs :: "rat le_constraint set"
    and p ::  "'i \<Rightarrow> linear_poly" 
    and co ::  "'i \<Rightarrow> rat" 
    and I :: "'i set" 
  defines "n \<equiv> \<lambda> i. Le_Constraint Leq_Rel (p i) (co i)" (* non-strict *)
    and "s \<equiv> \<lambda> i. Le_Constraint Lt_Rel (p i) (co i)"    (* strict *)
  assumes fin: "finite cs" "finite I" 
    and C: "C \<subseteq> cs \<union> s ` I" 
    and unsat: "\<nexists> v. \<forall> c \<in> C. v \<Turnstile>\<^sub>l\<^sub>e c" 
    and min: "\<And> D. D \<subset> C \<Longrightarrow> \<exists> v. \<forall> c \<in> D. v \<Turnstile>\<^sub>l\<^sub>e c" 
    and sol: "\<forall> c \<in> cs \<union> n ` I. v \<Turnstile>\<^sub>l\<^sub>e c" 
    and i: "i \<in> I" "s i \<in> C" 
  shows "(p i)\<lbrace>v\<rbrace> = co i" 
proof -
  have "finite ((cs \<union> s ` I) \<inter> C)" using fin by auto
  with C have finC: "finite C" by (simp add: inf_absorb2)
  from Motzkin's_transposition_theorem[OF this] unsat
  obtain D const rel where valid: "\<forall>(r, c)\<in>set D. 0 < r \<and> c \<in> C" and
        eq: "(\<Sum>(r, c)\<leftarrow>D. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) =
              Le_Constraint rel 0 const"
        and ineq: "rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0" by auto
  let ?expr = "(\<Sum>(r, c)\<leftarrow>D. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c))" 
  {
    assume "s i \<notin> snd ` set D"
    with valid have valid: "\<forall>(r, c)\<in>set D. 0 < r \<and> c \<in> C - {s i}"
      by force
    from finC have "finite (C - {s i})" by auto
    from Motzkin's_transposition_theorem[OF this] valid eq ineq
    have "\<nexists> v. \<forall>c\<in>C - {s i}. v \<Turnstile>\<^sub>l\<^sub>e c" by blast
    with min[of "C - {s i}"] i(2) have False by auto
  }
  hence mem: "s i \<in> snd ` set D" by auto
  from i(1) sol have "v \<Turnstile>\<^sub>l\<^sub>e  n i" by auto
  from this[unfolded n_def] have piv: "(p i) \<lbrace> v \<rbrace> \<le> co i" by simp
  from ineq have const0: "const \<le> 0" by auto
  define I' where "I' = cs \<union> n ` I"
  define f where "f c = (if c \<in> insert (s i) I' then c else (n (SOME j. j \<in> I \<and> s j = c)))" for c
  let ?C = "insert (s i) I'" 
  {
    fix c
    assume "c \<in> C" 
    hence c: "c \<in> cs \<union> s ` I" using C by auto
    hence "f c \<in> ?C \<and> lec_poly (f c) = lec_poly c \<and> lec_const (f c) = lec_const c"
    proof (cases "c \<in> cs \<union> n ` I \<union> {s i}")
      case True
      thus ?thesis unfolding f_def I'_def by auto
    next
      case False
      define j where "j = (SOME x. x \<in> I \<and> s x = c)" 
      from False have "\<exists> j. j \<in> I \<and> s j = c" using c by auto
      from someI_ex[OF this, folded j_def] have j: "j \<in> I" and c: "c = s j" by auto
      from False have fc: "f c = n j" unfolding f_def j_def[symmetric] I'_def by auto
      show ?thesis using j c fc by (auto simp: n_def s_def I'_def)
    qed
    hence "f c \<in> insert (s i) I'" "lec_poly (f c) = lec_poly c" "lec_const (f c) = lec_const c" 
      by auto
  } note f = this
  
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    with piv have "(p i)\<lbrace> v \<rbrace> < co i" by simp
    hence vsi: "v \<Turnstile>\<^sub>l\<^sub>e s i" unfolding s_def by auto  
    with sol have sol: "(\<exists> v. \<forall>c \<in> insert (s i) I'. v \<Turnstile>\<^sub>l\<^sub>e c) = True" unfolding I'_def by auto
    let ?D = "map (map_prod id f) D" 
    have fin: "finite (insert (s i) I')" unfolding I'_def using fin by auto
    from valid f(1)
    have valid': "\<forall>(r, c)\<in>set ?D. 0 < r \<and> c \<in> ?C" by force
    let ?expr' = "\<Sum>(r, c)\<leftarrow>?D. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)" 
    have "lec_const ?expr' = lec_const ?expr" 
      unfolding sum_list_lec
      apply simp
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl])
      using f valid by auto
    also have "\<dots> = const" unfolding eq by simp
    finally have const: "lec_const ?expr' = const" by auto
    have "lec_poly ?expr' = lec_poly ?expr" 
      unfolding sum_list_lec
      apply simp
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl])
      using f valid by auto
    also have "\<dots> = 0" unfolding eq by simp
    finally have poly: "lec_poly ?expr' = 0" by auto
    from mem obtain c where "(c, s i) \<in> set D" by auto
    hence "(c, f (s i)) \<in> set ?D" by force
    hence mem: "(c, s i) \<in> set ?D" unfolding f_def by auto
    moreover have "lec_rel (s i) = Lt_Rel" unfolding s_def by auto
    ultimately 
    have rel: "lec_rel ?expr' = Lt_Rel" 
      unfolding lec_rel_sum_list using split_list[OF mem] by fastforce
    have eq': "?expr' = Le_Constraint Lt_Rel 0 const" 
      using const poly rel by (simp add: sum_list_lec) 

    from valid' eq' Motzkin's_transposition_theorem[OF fin, unfolded sol] const0
    show False by blast
  qed
qed 

end