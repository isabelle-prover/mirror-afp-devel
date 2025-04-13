section\<open>Extensions for Existing AFP Entries\<close>

subsection\<open>First Order Terms\<close> 

theory Term_Impl
  imports
    First_Order_Terms.Term_More
    Certification_Monads.Check_Monad
    Deriving.Compare_Order_Instances
    Show.Shows_Literal
    FOR_Preliminaries
begin

derive compare_order "term"

subsubsection\<open>Positions\<close>
fun poss_list :: "('f, 'v) term \<Rightarrow> pos list"
  where
    "poss_list (Var x) = [[]]" |
    "poss_list (Fun f ss) = ([] # concat (map (\<lambda> (i, ps).
    map ((#) i) ps) (zip [0 ..< length ss] (map poss_list ss))))"

lemma poss_list_sound [simp]:
  "set (poss_list s) = poss s" 
proof (induct s)
  case (Fun f ss)
  let ?z = "zip [0..<length ss] (map poss_list ss)"
  have "(\<Union>a\<in>set ?z. set (case_prod (\<lambda>i. map ((#) i)) a)) = 
       {i # p |i p. i < length ss \<and> p \<in> poss (ss ! i)}" (is "?l = ?r")
  proof (rule set_eqI)
    fix ip
    show "(ip \<in> ?l) = (ip \<in> ?r)"
    proof
      assume "ip \<in> ?l" 
      from this obtain ipI where 
        z: "ipI \<in> set ?z" and 
        ip: "ip \<in> set (case_prod (\<lambda> i. map ((#) i)) ipI)" 
        by auto     
      from z obtain i where i: "i < length ?z" and zi: "?z ! i = ipI"
        by (force simp: set_conv_nth)      
      with ip Fun show "ip \<in> ?r" by auto
    next
      assume "ip \<in> ?r"
      from this obtain i p where i: "i < length ss" and "p \<in> poss (ss ! i)"
        and ip: "ip = i # p" by auto
      with Fun have p: "p \<in> set (poss_list (ss ! i))" and iz: "i < length ?z" by auto
      from i have id: "?z ! i = (i, poss_list (ss ! i))" (is "_ = ?ipI") by auto
      from iz have  "?z ! i \<in> set ?z" by (rule nth_mem)
      with id have inZ: "?ipI \<in> set ?z" by auto
      from p have "i # p \<in> set (case_prod (\<lambda> i. map ((#) i)) ?ipI)" by auto
      with inZ ip show "ip \<in> ?l" by force
    qed
  qed
  with Fun show ?case by simp
qed simp

declare poss_list.simps [simp del]

fun var_poss_list :: "('f, 'v) term \<Rightarrow> pos list"
  where
    "var_poss_list (Var x) = [[]]" |
    "var_poss_list (Fun f ss) = (concat (map (\<lambda> (i, ps).
    map ((#) i) ps) (zip [0 ..< length ss] (map var_poss_list ss))))"

(*more or less copied from poss_list_sound*)
lemma var_poss_list_sound [simp]:
  "set (var_poss_list s) = var_poss s"
proof (induct s)
  case (Fun f ss)
  let ?z = "zip [0..<length ss] (map var_poss_list ss)"
  have "(\<Union>a\<in>set ?z. set (case_prod (\<lambda>i. map ((#) i)) a)) = 
        (\<Union>i<length ss. {i # p |p. p \<in> var_poss (ss ! i)})" (is "?l = ?r")
  proof (rule set_eqI)
    fix ip
    show "(ip \<in> ?l) = (ip \<in> ?r)"
    proof
      assume "ip \<in> ?l" 
      from this obtain ipI where 
        z: "ipI \<in> set ?z" and 
        ip: "ip \<in> set (case_prod (\<lambda> i. map ((#) i)) ipI)" 
        by auto      
      from z obtain i where i: "i < length ?z" and zi: "?z ! i = ipI"
        by (force simp: set_conv_nth)      
      with ip Fun show "ip \<in> ?r" by auto
    next
      assume "ip \<in> ?r"
      from this obtain i p where i: "i < length ss" and "p \<in> var_poss (ss ! i)"
        and ip: "ip = i # p" by auto
      with Fun have p: "p \<in> set (var_poss_list (ss ! i))" and iz: "i < length ?z" by auto
      from i have id: "?z ! i = (i, var_poss_list (ss ! i))" (is "_ = ?ipI") by auto
      from iz have  "?z ! i \<in> set ?z" by (rule nth_mem)
      with id have inZ: "?ipI \<in> set ?z" by auto
      from p have "i # p \<in> set (case_prod (\<lambda> i. map ((#) i)) ?ipI)" by auto
      with inZ ip show "ip \<in> ?l" by force
    qed
  qed
  with Fun show ?case unfolding var_poss_list.simps by simp
qed simp

lemma length_var_poss_list: "length (var_poss_list t) = length (vars_term_list t)"
proof(induct t)
  case (Var x)
  then show ?case unfolding var_poss_list.simps vars_term_list.simps by simp
next
  case (Fun f ts)
  let ?xs="map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts)"
  let ?ys="map vars_term_list ts"
  have l1:"length ?xs = length ts"
    by simp  
  have l2:"length ?ys = length ts" 
    by simp
  {fix i assume i:"i < length ts"
    then have "(zip [0..<length ts] (map var_poss_list ts)) ! i = (i, var_poss_list (ts!i))" by simp 
    with i have "?xs!i = (map ((#) i)) (var_poss_list (ts!i))" by simp
    then have "length (?xs!i) = length (var_poss_list (ts!i))" by simp 
    with i have "length (?xs!i) = length (?ys!i)" using Fun.hyps by simp
  }
  then show ?case 
    unfolding var_poss_list.simps vars_term_list.simps using eq_length_concat_nth[of ?xs ?ys] l1 l2 by presburger  
qed

lemma vars_term_list_var_poss_list:
  assumes "i < length (vars_term_list t)" 
  shows "Var ((vars_term_list t)!i) = t|_((var_poss_list t)!i)"
  using assms proof(induct t arbitrary:i)
  case (Var x)
  then have i:"i = 0" 
    unfolding vars_term_list.simps by simp 
  then show ?case unfolding i vars_term_list.simps poss_list.simps var_poss.simps by simp
next
  case (Fun f ts)
  let ?xs="(map vars_term_list ts)"
  let ?ys="(map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts))"
  from Fun(2) have 1:"i < length (concat ?xs)" unfolding vars_term_list.simps by simp
  have 2:"length ?ys = length ?xs" unfolding length_map by simp
  {fix i assume i:"i < length ?xs"
    then have *:"(map2 (\<lambda>x. map ((#) x)) [0..<length ts] (map var_poss_list ts) ! i) = map ((#) i) (var_poss_list (ts!i))" 
      unfolding length_map by simp
    with i have "length (?ys ! i) = length (?xs ! i)"
      unfolding * length_map length_var_poss_list by simp
  }note l=this
  then obtain j k where j:"j < length ?xs" and k:"k < length (?xs ! j)" 
    and concat:"concat ?xs ! i = ?xs ! j ! k" "concat ?ys ! i = ?ys ! j ! k"
    using nth_concat_two_lists[OF 1 2] by blast 
  from Fun(1) j k have "Var (vars_term_list (ts!j) ! k) = (ts!j) |_ var_poss_list (ts!j) ! k" 
    unfolding length_map by force 
  then have "Var (vars_term_list (Fun f ts) ! i) = (Fun f ts)|_(j#(var_poss_list (ts!j) ! k))" 
    unfolding vars_term_list.simps concat(1) using j by auto 
  moreover have "j#(var_poss_list (ts!j) ! k) = ((var_poss_list (Fun f ts))!i)" proof-
    from k have "k < length (map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts) ! j)" 
      using l j by presburger 
    then show ?thesis 
      unfolding var_poss_list.simps concat(2) using j unfolding length_map by simp
  qed
  ultimately show ?case
    by presburger  
qed

lemma var_poss_list_map_vars_term:
  shows "var_poss_list (map_vars_term f t) = var_poss_list t"
proof(induct t)
  case (Fun g ts)
  then have IH:"map var_poss_list ts = map var_poss_list (map (map_vars_term f) ts)"
    by fastforce
  then show ?case unfolding map_vars_term_eq eval_term.simps IH var_poss_list.simps
    by force
qed simp

lemma distinct_var_poss_list:
  shows "distinct (var_poss_list t)"
proof(induct t)
  case (Fun f ts)
  let ?xs="(map2 (\<lambda>i. map ((#) i)) [0..<length ts] (map var_poss_list ts))"
  have l:"length ?xs = length ts"
    by force 
  have d1:"distinct (removeAll [] ?xs)" proof-
    have xs':"removeAll [] ?xs = filter (\<lambda>x. x \<noteq> []) ?xs"
      by (metis (mono_tags, lifting) filter_cong removeAll_filter_not_eq) 
    {fix i j assume i:"i < length ?xs" "?xs!i \<noteq> []" and j:"j < length ?xs" "?xs!j \<noteq> []" and ij:"i \<noteq> j"  
      from i l obtain p where p:"i#p \<in> set (?xs!i)" using nth_mem
        by (smt (z3) add.left_neutral diff_zero length_greater_0_conv length_map length_upt nth_map nth_upt nth_zip prod.simps(2))
      from l j(1) have "?xs ! j = map ((#) j) ((map var_poss_list ts)!j)"
        by simp 
      with p have "?xs!i \<noteq> ?xs!j" using ij by force
    }
    then show ?thesis using distinct_filter2 xs' by (smt (verit)) 
  qed
  {fix x assume "x \<in> set ?xs"
    with l obtain i where i:"i < length ts" and "x = ?xs!i" by (metis in_set_idx) 
    then have x:"x = map ((#) i) (var_poss_list (ts!i))" by simp 
    from Fun i have "distinct (var_poss_list (ts!i))" by auto 
    then have "distinct x" 
      unfolding x by (simp add: distinct_map)
  }note d2=this
  {fix x y assume "x \<in> set ?xs" "y \<in> set ?xs" "x \<noteq> y" 
    then obtain i j where i:"i < length ?xs" "x = ?xs!i" and j:"j < length ?xs" "y = ?xs!j" and ij:"i \<noteq> j"
      by (metis in_set_idx) 
    from i have x:"x = map ((#) i) (var_poss_list (ts!i))" by simp
    from j have y:"y = map ((#) j) (var_poss_list (ts!j))" by simp
    {fix p q assume p:"p \<in> set x" and q:"q \<in> set y" 
      from x p obtain p' where p':"p = i#p'" and "p' \<in> set (var_poss_list (ts!i))"  
        by auto
      from y q obtain q' where q':"q = j#q'" and "q' \<in> set (var_poss_list (ts!j))"  
        by auto
      from q' p' have "p \<noteq> q" by (simp add: ij) 
    }
    then have "set x \<inter> set y = {}" by auto
  }note d3=this
  from d1 d2 d3 show ?case unfolding var_poss_list.simps using distinct_concat_iff by blast 
qed simp

fun fun_poss_list :: "('f, 'v) term \<Rightarrow> pos list"
  where
    "fun_poss_list (Var x) = []" |
    "fun_poss_list (Fun f ss) = ([] # concat (map (\<lambda> (i, ps).
    map ((#) i) ps) (zip [0 ..< length ss] (map fun_poss_list ss))))"

lemma set_fun_poss_list [simp]:
  "set (fun_poss_list t) = fun_poss t"
  by (induct t; auto simp: UNION_set_zip)

context
begin
private fun in_poss :: "pos \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "in_poss [] _ \<longleftrightarrow> True" |
    "in_poss (Cons i p) (Fun f ts) \<longleftrightarrow> i < length ts \<and> in_poss p (ts ! i)" |
    "in_poss (Cons i p) (Var _) \<longleftrightarrow> False"

lemma poss_code[code_unfold]:
  "p \<in> poss t = in_poss p t" by (induct rule: in_poss.induct) auto
end

subsubsection\<open>List of Distinct Variables\<close>
text\<open>We introduce a duplicate free version of @{const vars_term_list} that preserves order of 
appearance of variables. This is used for the theory on proof terms.\<close>
  (*Looks complicated because of the way remdups is defined.*)
abbreviation vars_distinct :: "('f, 'v) term \<Rightarrow> 'v list" where "vars_distinct t \<equiv> (rev \<circ> remdups \<circ> rev) (vars_term_list t)"

lemma single_var[simp]: "vars_distinct (Var x) = [x]"
  by (simp add: vars_term_list.simps(1)) 

lemma vars_term_list_vars_distinct:
  assumes "i < length (vars_term_list t)"
  shows "\<exists>j < length (vars_distinct t). (vars_term_list t)!i = (vars_distinct t)!j"
  by (metis assms in_set_idx nth_mem o_apply set_remdups set_rev)

subsubsection \<open>Useful abstractions\<close>

text \<open>Given that we perform the same operations on terms in order to get
a list of the variables and a list of the functions, we define functions
that run through the term and perform these actions.\<close>

context
begin
private fun contains_var_term :: "'v \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "contains_var_term x (Var y) = (x = y)"
| "contains_var_term x (Fun _ ts) = Bex (set ts) (contains_var_term x)"

lemma contains_var_term_sound[simp]:
  "contains_var_term x t \<longleftrightarrow> x \<in> vars_term t"
  by (induct t) auto

(*use efficient implementation for code-generation*)
lemma in_vars_term_code[code_unfold]: "x \<in> vars_term t = contains_var_term x t" by simp
end

subsubsection\<open>Linear Terms\<close>

lemma distinct_vars_linear_term:
  assumes "distinct (vars_term_list t)"
  shows "linear_term t"
  using assms proof(induct t)
  case (Fun f ts)
  {fix t' assume t':"t' \<in> set ts"
    with Fun(2) have "distinct (vars_term_list t')" 
      unfolding vars_term_list.simps by (simp add: distinct_concat_iff)
    with Fun(1) t' have "linear_term t'" by auto
  }note IH=this
  have "is_partition (map (set \<circ> vars_term_list) ts)" 
    using distinct_is_partitition_sets vars_term_list.simps(2) Fun(2) by force 
  then have "is_partition (map vars_term ts)" by (simp add: comp_def) 
  with IH show ?case by simp
qed simp

fun
  linear_term_impl :: "'v set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('v set) option"
  where
    "linear_term_impl xs (Var x) = (if x \<in> xs then None else Some (insert x xs))" |
    "linear_term_impl xs (Fun _ []) = Some xs" |
    "linear_term_impl xs (Fun f (t # ts)) = (case linear_term_impl xs t of 
    None \<Rightarrow> None
  | Some ys \<Rightarrow> linear_term_impl ys (Fun f ts))"

lemma linear_term_code[code]: "linear_term t = (linear_term_impl {} t \<noteq> None)" 
proof -
  {
    note [simp] = is_partition_Nil is_partition_Cons
    fix xs ys
    let ?P = "\<lambda> ys xs t. (linear_term_impl xs t = None \<longrightarrow> (xs \<inter> vars_term t \<noteq> {} \<or> \<not> linear_term t)) \<and> 
      (linear_term_impl xs t = Some ys \<longrightarrow> (ys = (xs \<union> vars_term t)) \<and> xs \<inter> vars_term t = {} \<and> linear_term t)"
    have "?P ys xs t"
    proof (induct rule: linear_term_impl.induct[of "\<lambda> xs t. \<forall> ys. ?P ys xs t", rule_format])
      case (3 xs f t ts zs)
      show ?case 
      proof (cases "linear_term_impl xs t")
        case None
        with 3 show ?thesis by auto
      next
        case (Some ys)
        note some = this
        with 3 have rec1: "ys = xs \<union> vars_term t \<and> xs \<inter> vars_term t = {} \<and> linear_term t" by auto
        show ?thesis 
        proof (cases "linear_term_impl ys (Fun f ts)")
          case None 
          with rec1 Some have res: "linear_term_impl xs (Fun f (t # ts)) = None" by simp
          from None 3(2) Some have rec2: "ys \<inter> vars_term (Fun f ts) \<noteq> {} \<or> \<not> linear_term (Fun f ts)" by simp
          then have "xs \<inter> vars_term (Fun f (t # ts)) \<noteq> {} \<or> \<not> linear_term (Fun f (t # ts))" 
          proof 
            assume "ys \<inter> vars_term (Fun f ts) \<noteq> {}" 
            then obtain x where x1: "x \<in> ys" and x2: "x \<in> vars_term (Fun f ts)" by auto
            show ?thesis 
            proof (cases "x \<in> xs")
              case True
              with x2 show ?thesis by auto
            next
              case False
              with x1 rec1 have "x \<in> vars_term t" by auto
              with x2 have "\<not> linear_term (Fun f (t # ts))" by auto
              then show ?thesis ..
            qed
          next
            assume "\<not> linear_term (Fun f ts)" then have "\<not> linear_term (Fun f (t # ts))" by auto
            then show ?thesis ..
          qed            
          with res show ?thesis by auto
        next
          case (Some us)
          with some have res: "linear_term_impl xs (Fun f (t # ts)) = Some us" by auto          
          {
            assume us: "us = zs"
            from Some[simplified us] 3(2) some 
            have rec2: "zs = ys \<union> vars_term (Fun f ts) \<and> ys \<inter> vars_term (Fun f ts) = {} \<and> linear_term (Fun f ts)" by auto
            from rec1 rec2  
            have part1: "zs = xs \<union> vars_term (Fun f (t # ts)) \<and> xs \<inter> vars_term (Fun f (t # ts)) = {}" (is ?part1) by auto
            from rec1 rec2 have "vars_term t \<inter> vars_term (Fun f ts) = {}" and "linear_term t" and "linear_term (Fun f ts)" by auto
            then have "linear_term (Fun f (t # ts))" (is ?part2) by auto 
            with part1 have "?part1 \<and> ?part2" ..
          }
          with res show ?thesis by auto
        qed
      qed
    qed auto
  } note main = this
  from main[of "{}"] show ?thesis by (cases "linear_term_impl {} t", auto)
qed

definition check_linear_term :: "('f :: showl, 'v :: showl) term \<Rightarrow> showsl check"
  where
    "check_linear_term s = check (linear_term s)
    (showsl (STR ''the term '') \<circ> showsl s \<circ> showsl (STR '' is not linear\<newline>''))"

lemma check_linear_term [simp]:
  "isOK (check_linear_term s) = linear_term s"
  by (simp add: check_linear_term_def)

subsubsection\<open>Subterms\<close>
fun supteq_list :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "supteq_list (Var x) = [Var x]" |
    "supteq_list (Fun f ts) = Fun f ts # concat (map supteq_list ts)"

fun supt_list :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "supt_list (Var x) = []" |
    "supt_list (Fun f ts) = concat (map supteq_list ts)"

lemma supteq_list [simp]:
  "set (supteq_list t) = {s. t \<unrhd> s}"
proof (rule set_eqI, unfold mem_Collect_eq)
  fix s
  show "s \<in> set(supteq_list t) = (t \<unrhd> s)"
  proof (induct t)
    case (Fun f ss)
    show ?case
    proof (cases "Fun f ss = s")
      case False
      show ?thesis
      proof
        assume "Fun f ss \<unrhd> s"
        with False have sup: "Fun f ss \<rhd> s" using supteq_supt_conv by auto
        obtain C where "C \<noteq> \<box>" and "Fun f ss = C\<langle>s\<rangle>" using sup by auto
        then obtain b D a where "Fun f ss = Fun f (b @ D\<langle>s\<rangle> # a)" by (cases C, auto)
        then have D: "D\<langle>s\<rangle> \<in> set ss" by auto
        with Fun[OF D] ctxt_imp_supteq[of D s] obtain t where "t \<in> set ss" and "s \<in> set (supteq_list t)" by auto
        then show "s \<in> set (supteq_list (Fun f ss))" by auto
      next
        assume "s \<in> set (supteq_list (Fun f ss))"
        with False obtain t where t: "t \<in> set ss" and "s \<in> set (supteq_list t)" by auto
        with Fun[OF t] have "t \<unrhd> s" by auto
        with t show "Fun f ss \<unrhd> s" by auto
      qed
    qed auto
  qed (simp add: supteq_var_imp_eq)
qed

lemma supt_list_sound [simp]:
  "set (supt_list t) = {s. t \<rhd> s}"
  by (cases t) auto

fun supt_impl :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "supt_impl (Var x) t \<longleftrightarrow> False" |
    "supt_impl (Fun f ss) t \<longleftrightarrow> t \<in> set ss \<or> Bex (set ss) (\<lambda>s. supt_impl s t)"

lemma supt_impl [code_unfold]:
  "s \<rhd> t \<longleftrightarrow> supt_impl s t"
proof
  assume "s \<rhd> t" then show "supt_impl s t"
  proof (induct s)
    case (Var x) then show ?case by auto
  next
    case (Fun f ss) then show ?case
    proof (cases "t \<in> set ss")
      case True then show ?thesis by (simp)
    next
      case False
      assume "\<And>s. \<lbrakk>s \<in> set ss; s \<rhd> t\<rbrakk> \<Longrightarrow> supt_impl s t"
        and "Fun f ss \<rhd> t" and "t \<notin> set ss"
      moreover from \<open>Fun f ss \<rhd> t\<close> obtain s where "s \<in> set ss" and "s \<rhd> t"
        by (cases rule: supt.cases) (simp_all add: \<open>t \<notin> set ss\<close>)
      ultimately have "supt_impl s t" by simp
      with \<open>s \<in> set ss\<close> show ?thesis by auto
    qed
  qed
next
  assume "supt_impl s t"
  then show "s \<rhd> t"
  proof (induct s)
    case (Var x) then show ?case by simp
  next
    case (Fun f ss)
    then have "t \<in> set ss \<or> (\<exists>s\<in>set ss. supt_impl s t)" by simp
    then show ?case
    proof
      assume "t \<in> set ss" then show ?case by auto
    next
      assume "\<exists>s\<in>set ss. supt_impl s t"
      then obtain s where "s \<in> set ss" and "supt_impl s t" by auto
      with Fun have "s \<rhd> t" by auto
      with \<open>s \<in> set ss\<close> show ?thesis by auto
    qed
  qed
qed

lemma supteq_impl[code_unfold]: "s \<unrhd> t \<longleftrightarrow> s = t \<or> supt_impl s t"
  unfolding supteq_supt_set_conv
  by (auto simp: supt_impl)

definition check_no_var :: "('f::showl, 'v::showl) term \<Rightarrow> showsl check" where
  "check_no_var t \<equiv> check (is_Fun t) (showsl (STR ''variable found\<newline>''))"

lemma check_no_var_sound[simp]:
  "isOK (check_no_var t) \<longleftrightarrow> is_Fun t"
  unfolding check_no_var_def by simp


definition
  check_supt :: "('f::showl, 'v::showl) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  where
    "check_supt s t \<equiv> check (s \<rhd> t) (showsl t \<circ> showsl (STR '' is not a proper subterm of '') \<circ> showsl s)"

definition
  check_supteq :: "('f::showl, 'v::showl) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  where
    "check_supteq s t \<equiv> check (s \<unrhd> t) (showsl t \<circ> showsl (STR '' is not a subterm of '') \<circ> showsl s)"

lemma isOK_check_supt [simp]:
  "isOK (check_supt s t) \<longleftrightarrow> s \<rhd> t"
  by (auto simp: check_supt_def)

lemma isOK_check_supteq [simp]:
  "isOK (check_supteq s t) \<longleftrightarrow> s \<unrhd> t"
  by (auto simp: check_supteq_def)

subsubsection \<open>Additional Functions on Terms\<close>

fun with_arity :: "('f, 'v) term \<Rightarrow> ('f \<times> nat, 'v) term" where
  "with_arity (Var x) = Var x"
| "with_arity (Fun f ts) = Fun (f, length ts) (map with_arity ts)"

fun add_vars_term :: "('f, 'v) term \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
    "add_vars_term (Var x) xs = x # xs" |
    "add_vars_term (Fun _ ts) xs = foldr add_vars_term ts xs"

fun add_funs_term :: "('f, 'v) term \<Rightarrow> 'f list \<Rightarrow> 'f list"
  where
    "add_funs_term (Var _) fs = fs" |
    "add_funs_term (Fun f ts) fs = f # foldr add_funs_term ts fs"

fun add_funas_term :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "add_funas_term (Var _) fs = fs" |
    "add_funas_term (Fun f ts) fs = (f, length ts) # foldr add_funas_term ts fs"

definition add_funas_args_term :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "add_funas_args_term t fs = foldr add_funas_term (args t) fs"

lemma add_vars_term_vars_term_list_conv [simp]:
  "add_vars_term t xs = vars_term_list t @ xs"
proof (induct t arbitrary: xs)
  case (Fun f ts)
  then show ?case by (induct ts) (simp_all add: vars_term_list.simps)
qed (simp add: vars_term_list.simps)

lemma add_funs_term_funs_term_list_conv [simp]:
  "add_funs_term t fs = funs_term_list t @ fs"
proof (induct t arbitrary: fs)
  case (Fun f ts)
  then show ?case by (induct ts) (simp_all add: funs_term_list.simps)
qed (simp add: funs_term_list.simps)

lemma add_funas_term_funas_term_list_conv [simp]:
  "add_funas_term t fs = funas_term_list t @ fs"
proof (induct t arbitrary: fs)
  case (Fun f ts)
  then show ?case by (induct ts) (simp_all add: funas_term_list.simps)
qed (simp add: funas_term_list.simps)

lemma add_vars_term_vars_term_list_abs_conv [simp]:
  "add_vars_term = (@) \<circ> vars_term_list"
  by (intro ext) simp

lemma add_funs_term_funs_term_list_abs_conv [simp]:
  "add_funs_term = (@) \<circ> funs_term_list"
  by (intro ext) simp

lemma add_funas_term_funas_term_list_abs_conv [simp]:
  "add_funas_term = (@) \<circ> funas_term_list"
  by (intro ext) simp

lemma add_funas_args_term_funas_args_term_list_conv [simp]:
  "add_funas_args_term t fs = funas_args_term_list t @ fs"
  by (simp add: add_funas_args_term_def funas_args_term_list_def concat_conv_foldr foldr_map)

fun insert_vars_term :: "('f, 'v) term \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
    "insert_vars_term (Var x) xs = List.insert x xs" |
    "insert_vars_term (Fun f ts) xs = foldr insert_vars_term ts xs"

fun insert_funs_term :: "('f, 'v) term \<Rightarrow> 'f list \<Rightarrow> 'f list"
  where
    "insert_funs_term (Var x) fs = fs" |
    "insert_funs_term (Fun f ts) fs = List.insert f (foldr insert_funs_term ts fs)"

fun insert_funas_term :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_term (Var x) fs = fs" |
    "insert_funas_term (Fun f ts) fs = List.insert (f, length ts) (foldr insert_funas_term ts fs)"

definition insert_funas_args_term :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_args_term t fs = foldr insert_funas_term (args t) fs"

lemma set_insert_vars_term_vars_term [simp]:
  "set (insert_vars_term t xs) = vars_term t \<union> set xs"
proof (induct t arbitrary: xs)
  case (Fun f ts)
  then show ?case by (induct ts) auto
qed simp

lemma set_insert_funs_term_funs_term [simp]:
  "set (insert_funs_term t fs) = funs_term t \<union> set fs"
proof (induct t arbitrary: fs)
  case (Fun f ts)
  then show ?case by (induct ts) auto
qed simp

lemma set_insert_funas_term_funas_term [simp]:
  "set (insert_funas_term t fs) = funas_term t \<union> set fs"
proof (induct t arbitrary: fs)
  case (Fun f ts)
  then have "set (foldr insert_funas_term ts fs) = \<Union> (funas_term ` set ts) \<union> set fs"
    by (induct ts) auto
  then show ?case by simp
qed simp

lemma set_insert_funas_args_term [simp]:
  "set (insert_funas_args_term t fs) = \<Union> (funas_term ` set (args t)) \<union> set fs"
proof (induct t arbitrary: fs)
  case (Fun f ts)
  then show ?case by (induct ts) (auto simp: insert_funas_args_term_def)
qed (simp add: insert_funas_args_term_def)

text \<open>Implementations of corresponding set-based functions.\<close>
abbreviation "vars_term_impl t \<equiv> insert_vars_term t []"
abbreviation "funs_term_impl t \<equiv> insert_funs_term t []"
abbreviation "funas_term_impl t \<equiv> insert_funas_term t []"

lemma vars_funs_term_list_code[code]:
  "vars_term_list t = add_vars_term t []"
  "funs_term_list t = add_funs_term t []"
  by simp_all

(*FIXME: define funas via with_arity and add_funs*)

lemma with_arity_term_fold [code]:
  "with_arity = Term_More.fold Var (\<lambda>f ts. Fun (f, length ts) ts)"
proof
  fix t :: "('f, 'v) term" 
  show "with_arity t = Term_More.fold Var (\<lambda>f ts. Fun (f, length ts) ts) t"
    by (induct t) simp_all
qed

fun flatten_term_enum :: "('f list, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "flatten_term_enum (Var x) = [Var x]" |
    "flatten_term_enum (Fun fs ts) =
    (let
      lts = map flatten_term_enum ts;
      ss = concat_lists lts
    in concat (map (\<lambda> f. map (Fun f) ss) fs))"

lemma flatten_term_enum: 
  "set (flatten_term_enum t) = {u. instance_term u (map_funs_term set t)}"
proof (induct t)
  case (Var x)
  show ?case (is "_ = ?R")
  proof -
    {
      fix t 
      assume "t \<in> ?R"
      then have "t = Var x" by (cases t, auto)
    } 
    then show ?thesis by auto
  qed
next
  case (Fun fs ts)
  show ?case (is "?L = ?R")
  proof -
    {
      fix i
      assume "i < length ts"
      then have "ts ! i \<in> set ts" by auto
      note Fun[OF this]
    } note ind = this
    have idL: "?L = {Fun g ss | g ss. g \<in> set fs  \<and> length ss = length ts \<and> (\<forall>i<length ts. ss ! i \<in> set (flatten_term_enum (ts ! i)))}" (is "_ = ?M1") by auto  
    let ?R1 = "{Fun f ss | f ss. f \<in> set fs \<and> length ss = length ts \<and> (\<forall> i<length ss. instance_term (ss ! i) (map_funs_term set (ts ! i)))}"
    {
      fix u
      assume "u \<in> ?R"
      then have "u \<in> ?R1" by (cases u, auto)
    }
    then have idR: "?R = ?R1" by auto
    show ?case unfolding idL idR using ind by auto
  qed
qed

definition check_ground_term :: "('f :: showl, 'v :: showl) term \<Rightarrow> showsl check"
  where
    "check_ground_term s = check (ground s)
    (showsl (STR ''the term '') \<circ> showsl s \<circ> showsl (STR '' is not a ground term\<newline>''))"

lemma check_ground_term [simp]:
  "isOK (check_ground_term s) \<longleftrightarrow> ground s"
  by (simp add: check_ground_term_def)

type_synonym 'f sig_list = "('f \<times> nat)list" 

fun check_funas_term :: "'f :: showl sig \<Rightarrow> ('f,'v :: showl)term \<Rightarrow> showsl check" where
  "check_funas_term F (Fun f ts) = do {
      check ((f, length ts) \<in> F) (showsl (Fun f ts) 
         o showsl_lit (STR ''problem: root of subterm  '') o showsl f o showsl_lit (STR '' not in signature\<newline>''));
      check_allm (check_funas_term F) ts
    }" 
| "check_funas_term F (Var _) = return ()" 

lemma check_funas_term[simp]: "isOK(check_funas_term F t) = (funas_term t \<subseteq> F)" 
  by (induct t, auto)

subsubsection\<open>Substitutions\<close>

definition mk_subst_domain :: "('f, 'v) substL \<Rightarrow> ('v \<times> ('f, 'v) term) list" where
  "mk_subst_domain \<sigma> \<equiv>
    let \<tau> = mk_subst Var \<sigma> in
    (filter (\<lambda>(x, t). Var x \<noteq> t) (map (\<lambda> x. (x, \<tau> x)) (remdups (map fst \<sigma>))))"

lemma mk_subst_domain:
  "set (mk_subst_domain \<sigma>) = (\<lambda> x. (x, mk_subst Var \<sigma> x)) ` subst_domain (mk_subst Var \<sigma>)"
  (is "?I = ?R")
proof -
  have "?I \<subseteq> ?R" unfolding mk_subst_domain_def Let_def subst_domain_def by auto
  moreover 
  {
    fix xt
    assume mem: "xt \<in> ?R"    
    obtain x t where xt: "xt = (x, t)" by force
    from mem [unfolded xt]
    have x: "x \<in> subst_domain (mk_subst Var \<sigma>)" and t: "t = mk_subst Var \<sigma> x" by auto
    then have "mk_subst Var \<sigma> x \<noteq> Var x" unfolding subst_domain_def by simp
    with t have l: "map_of \<sigma> x = Some t" and tx: "t \<noteq> Var x" 
      unfolding mk_subst_def by (cases "map_of \<sigma> x", auto)
    from map_of_SomeD[OF l] l t tx have "(x,t) \<in> ?I" unfolding mk_subst_domain_def Let_def
      by force
    then have "xt \<in> ?I" unfolding xt .
  }
  ultimately show ?thesis by blast
qed

lemma finite_mk_subst: "finite (subst_domain (mk_subst Var \<sigma>))"
proof -
  have "subst_domain (mk_subst Var \<sigma>) = fst ` set (mk_subst_domain \<sigma>)"
    unfolding mk_subst_domain Let_def by force
  moreover have "finite ..."
    using finite_set by auto
  ultimately show ?thesis by simp
qed

definition subst_eq :: "('f, 'v) substL \<Rightarrow> ('f, 'v) substL \<Rightarrow> bool" where
  "subst_eq \<sigma> \<tau> = (let \<sigma>' = mk_subst_domain \<sigma>; \<tau>' = mk_subst_domain \<tau> in set \<sigma>' = set \<tau>')"  

lemma subst_eq [simp]:
  "subst_eq \<sigma> \<tau> = (mk_subst Var \<sigma> = mk_subst Var \<tau>)"
proof -
  let ?\<sigma> = "mk_subst Var \<sigma>"
  let ?\<tau> = "mk_subst Var \<tau>"
  {
    assume id: "((\<lambda> x. (x, ?\<sigma> x)) ` subst_domain ?\<sigma>) =  ((\<lambda> x. (x, ?\<tau> x)) ` subst_domain ?\<tau>)" (is "?l = ?r")
    from arg_cong[OF id, of "(`) fst"] have idd: "subst_domain ?\<sigma> = subst_domain ?\<tau>" by force
    have "?\<sigma> = ?\<tau>" 
    proof (rule ext)
      fix x
      show "?\<sigma> x = ?\<tau> x"
      proof (cases "x \<in> subst_domain ?\<sigma>")
        case False
        then show ?thesis using idd unfolding subst_domain_def by auto
      next
        case True
        with idd have x: "(x,?\<sigma> x) \<in> ?l" "(x,?\<tau> x) \<in> ?r" by auto
        with id have x: "(x,?\<tau> x) \<in> ?l" "(x,?\<sigma> x) \<in> ?l" by auto
        then show ?thesis by auto
      qed
    qed
  }
  then show ?thesis 
    unfolding subst_eq_def Let_def
    unfolding mk_subst_domain by auto
qed

definition range_vars_impl :: "('f, 'v) substL \<Rightarrow> 'v list"
  where 
    "range_vars_impl \<sigma> =
    (let \<sigma>' = mk_subst_domain \<sigma> in  
    concat (map (vars_term_list o snd) \<sigma>'))"

definition vars_subst_impl :: "('f, 'v) substL \<Rightarrow> 'v list"
  where 
    "vars_subst_impl \<sigma> =
    (let \<sigma>' = mk_subst_domain \<sigma> in
    map fst \<sigma>' @ concat (map (vars_term_list o snd) \<sigma>'))"

lemma vars_subst_impl [simp]:
  "set (vars_subst_impl \<sigma>) = vars_subst (mk_subst Var \<sigma>)"
  unfolding vars_subst_def vars_subst_impl_def Let_def 
  by (auto simp: mk_subst_domain, force)

lemma range_vars_impl [simp]:
  "set (range_vars_impl \<sigma>) = range_vars (mk_subst Var \<sigma>)"
  unfolding range_vars_def range_vars_impl_def Let_def 
  by (auto simp: mk_subst_domain)

lemma mk_subst_one [simp]: "mk_subst Var [(x, t)] = subst x t"
  unfolding mk_subst_def subst_def by auto

lemma fst_image [simp]: "fst ` (\<lambda> x. (x,g x)) ` a = a" by force

definition
  subst_compose_impl :: "('f, 'v) substL \<Rightarrow> ('f, 'v) substL \<Rightarrow> ('f, 'v) substL"
  where
    "subst_compose_impl \<sigma> \<tau> \<equiv> 
  let
    \<sigma>' = mk_subst_domain \<sigma>; 
    \<tau>' = mk_subst_domain \<tau>;
    d\<sigma> = map fst \<sigma>'
  in map (\<lambda> (x, t). (x, t \<cdot> mk_subst Var \<tau>')) \<sigma>' @ filter (\<lambda> (x, t). x \<notin> set d\<sigma>) \<tau>'"

lemma mk_subst_mk_subst_domain [simp]:
  "mk_subst Var (mk_subst_domain \<sigma>) = mk_subst Var \<sigma>"
proof (intro ext)
  fix x
  {
    assume x: "x \<notin> subst_domain (mk_subst Var \<sigma>)"
    then have \<sigma>: "mk_subst Var \<sigma> x = Var x" unfolding subst_domain_def by auto
    from x have "x \<notin> fst ` set (mk_subst_domain \<sigma>)" unfolding mk_subst_domain by auto
    then have look: "map_of (mk_subst_domain \<sigma>) x = None" by (cases "map_of (mk_subst_domain \<sigma>) x", insert map_of_SomeD[of "mk_subst_domain \<sigma>" x], force+)
    then have "mk_subst Var (mk_subst_domain \<sigma>) x = mk_subst Var \<sigma> x" unfolding \<sigma>
      unfolding mk_subst_def by auto
  } note ndom = this
  {
    assume "x \<in> subst_domain (mk_subst Var \<sigma>)"
    then have "x \<in> fst ` set (mk_subst_domain \<sigma>)" unfolding mk_subst_domain by auto
    then obtain t where look: "map_of (mk_subst_domain \<sigma>) x = Some t" by (cases "map_of (mk_subst_domain \<sigma>) x", (force simp: map_of_eq_None_iff)+)
    from map_of_SomeD[OF look, unfolded mk_subst_domain] have t: "t = mk_subst Var \<sigma> x" by auto
    from look t have res: "mk_subst Var (mk_subst_domain \<sigma>) x = mk_subst Var \<sigma> x" unfolding mk_subst_def by auto
  } note dom = this
  from ndom dom
  show "mk_subst Var (mk_subst_domain \<sigma>) x = mk_subst Var \<sigma> x" by auto
qed

lemma subst_compose_impl [simp]:
  "mk_subst Var (subst_compose_impl \<sigma> \<tau>) = mk_subst Var \<sigma> \<circ>\<^sub>s mk_subst Var \<tau>" (is "?l = ?r")
proof (rule ext)
  fix x
  let ?\<sigma> = "mk_subst Var \<sigma>"
  let ?\<tau> = "mk_subst Var \<tau>"
  let ?s = "map (\<lambda> (x, t). (x, t \<cdot> mk_subst Var (mk_subst_domain \<tau>))) (mk_subst_domain \<sigma>)"
  let ?t = "[(x,t) \<leftarrow> mk_subst_domain \<tau>. x \<notin> set (map fst (mk_subst_domain \<sigma>))]"
  note d = subst_compose_impl_def[unfolded Let_def]
  show "?l x = ?r x"
  proof (cases "x \<in> subst_domain (mk_subst Var \<sigma>)")
    case True
    then have "?\<sigma> x \<noteq> Var x" unfolding subst_domain_def by auto
    then obtain t where look: "map_of \<sigma> x = Some t" and \<sigma>: "?\<sigma> x = t"
      unfolding mk_subst_def by (cases "map_of \<sigma> x", auto)
    from \<sigma> have r: "?r x = t \<cdot> ?\<tau>" unfolding subst_compose_def by simp
    from True have "x \<in> subst_domain (mk_subst Var (mk_subst_domain \<sigma>))" 
      by simp
    from \<sigma> True  have mem: "(x,t \<cdot> ?\<tau>) \<in> set ?s" by (auto simp: mk_subst_domain)
    with map_of_eq_None_iff[of "?s" x]
    obtain u where look2: "map_of ?s x = Some u"
      by (cases "map_of ?s x", force+)
    from map_of_SomeD[OF this] \<sigma> have u: "u = t \<cdot> ?\<tau>" 
      by (auto simp: mk_subst_domain)
    note look2 = map_of_append_Some[OF look2, of ?t]
    have l: "?l x = t \<cdot> ?\<tau>" unfolding d mk_subst_def[of Var "?s @ ?t"] look2 u
      by simp
    from l r show ?thesis by simp
  next
    case False
    then have \<sigma>: "?\<sigma> x = Var x" unfolding subst_domain_def by auto
    from \<sigma> have r: "?r x = ?\<tau> x" unfolding subst_compose_def by simp
    from False have "x \<notin> subst_domain (mk_subst Var (mk_subst_domain \<sigma>))" 
      by simp
    from False  have mem: "\<And> y. (x,y) \<notin> set ?s" by (auto simp: mk_subst_domain)
    with map_of_SomeD[of ?s x] have look2: "map_of ?s x = None"
      by (cases "map_of ?s x", auto)
    note look2 = map_of_append_None[OF look2, of ?t]
    have l: "?l x = (case map_of ?t x of None \<Rightarrow> Var x | Some t \<Rightarrow> t)" unfolding d mk_subst_def[of Var "?s @ ?t"] look2 by simp
    also have "... = ?\<tau> x"
    proof (cases "x \<in> subst_domain ?\<tau>")
      case True
      then have "?\<tau> x \<noteq> Var x" unfolding subst_domain_def by auto
      then obtain t where look: "map_of \<tau> x = Some t" and \<tau>: "?\<tau> x = t"
        unfolding mk_subst_def by (cases "map_of \<tau> x", auto)
      from True have "x \<in> subst_domain (mk_subst Var (mk_subst_domain \<tau>))" 
        by simp
      from \<tau> True  have mem: "(x,?\<tau> x) \<in> set ?t" using False by (auto simp: mk_subst_domain)
      with map_of_eq_None_iff[of ?t x] obtain u where look2: "map_of ?t x = Some u"
        by (cases "map_of ?t x", force+)
      from map_of_SomeD[OF this] \<tau> have u: "u = ?\<tau> x" 
        by (auto simp: mk_subst_domain)
      show ?thesis using look2 u by simp
    next
      case False
      then have \<tau>: "?\<tau> x = Var x" unfolding subst_domain_def by auto
      from False have "x \<notin> subst_domain (mk_subst Var (mk_subst_domain \<tau>))" 
        by simp
      from False have mem: "\<And> y. (x,y) \<notin> set ?t" by (auto simp: mk_subst_domain)
      with map_of_SomeD[of ?t x] have look2: "map_of ?t x = None"
        by (cases "map_of ?t x", auto)
      show ?thesis unfolding \<tau> look2 by simp
    qed
    finally show ?thesis unfolding r by simp
  qed
qed

fun subst_power_impl :: "('f, 'v) substL \<Rightarrow> nat \<Rightarrow> ('f, 'v) substL" where
  "subst_power_impl \<sigma> 0 = []"
| "subst_power_impl \<sigma> (Suc n) = subst_compose_impl \<sigma> (subst_power_impl \<sigma> n)"

lemma subst_power_impl [simp]:
  "mk_subst Var (subst_power_impl \<sigma> n) = (mk_subst Var \<sigma>)^^n"
  by (induct n, auto)

definition commutes_impl :: "('f, 'v) substL \<Rightarrow> ('f, 'v) substL \<Rightarrow> bool" where
  "commutes_impl \<sigma> \<mu> \<equiv> subst_eq (subst_compose_impl \<sigma> \<mu>) (subst_compose_impl \<mu> \<sigma>)"

lemma commutes_impl [simp]:
  "commutes_impl \<sigma> \<mu> = ((mk_subst Var \<sigma> \<circ>\<^sub>s mk_subst Var \<mu>) = (mk_subst Var \<mu> \<circ>\<^sub>s mk_subst Var \<sigma>))"
  unfolding commutes_impl_def by simp

definition
  subst_compose'_impl :: "('f, 'v) substL \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) substL"
  where
    "subst_compose'_impl \<sigma> \<rho> \<equiv> map (\<lambda> (x, s). (x, s \<cdot> \<rho>)) (mk_subst_domain \<sigma>)"

lemma subst_compose'_impl [simp]:
  "mk_subst Var (subst_compose'_impl \<sigma> \<rho>) = subst_compose' (mk_subst Var \<sigma>) \<rho>" (is "?l = ?r")
proof (rule ext)
  fix x
  note d = subst_compose'_def subst_compose'_impl_def 
  let ?\<sigma> = "mk_subst Var \<sigma>"
  let ?s = "subst_compose'_impl \<sigma> \<rho>"
  show "?l x = ?r x"
  proof (cases "x \<in> subst_domain (mk_subst Var \<sigma>)")
    case True
    then have r: "?r x = ?\<sigma> x \<cdot> \<rho>" unfolding d by simp
    from True have "(x, ?\<sigma> x) \<in> set (mk_subst_domain \<sigma>)" unfolding mk_subst_domain by auto
    then have "(x, ?\<sigma> x \<cdot> \<rho>) \<in> set ?s" unfolding d by auto
    with map_of_eq_None_iff[of ?s x] obtain u where look: "map_of ?s x = Some u"
      by (cases "map_of ?s x", force+)
    from map_of_SomeD[OF this] have u: "u = ?\<sigma> x \<cdot> \<rho>" unfolding d using mk_subst_domain[of \<sigma>] by auto
    then have l: "?l x = ?\<sigma> x \<cdot> \<rho>" using look u unfolding mk_subst_def by auto
    from l r show ?thesis by simp
  next
    case False
    then have r: "?r x = Var x" unfolding d by simp
    from False have "\<And> y. (x,y) \<notin> set ?s" unfolding d 
      by (auto simp: mk_subst_domain)
    with map_of_SomeD[of ?s x] have look: "map_of ?s x = None" 
      by (cases "map_of ?s x", auto)
    then have l: "?l x = Var x" unfolding mk_subst_def by simp
    from l r show ?thesis by simp
  qed
qed

definition
  subst_replace_impl :: "('f, 'v) substL \<Rightarrow> 'v \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) substL"
  where
    "subst_replace_impl \<sigma> x t \<equiv> (x, t) # filter (\<lambda> (y, t). y \<noteq> x) \<sigma>"

lemma subst_replace_impl [simp]:
  "mk_subst Var (subst_replace_impl \<sigma> x t) = (\<lambda> y. if x = y then t else mk_subst Var \<sigma> y)" (is "?l = ?r")
proof (rule ext)
  fix y
  note d = subst_replace_impl_def
  show "?l y = ?r y"
  proof (cases "y = x")
    case True
    then show ?thesis unfolding d mk_subst_def by auto
  next
    case False
    let ?\<sigma> = "mk_subst Var \<sigma>"
    from False have r: "?r y = ?\<sigma> y" by auto
    from False have l: "?l y =  mk_subst Var ([(y, t)\<leftarrow>\<sigma> . y \<noteq> x]) y" unfolding mk_subst_def d
      by simp
    also have "... = ?\<sigma> y" unfolding mk_subst_def  
      using map_of_filter[of "\<lambda> y. y \<noteq> x" y \<sigma>, OF False] by simp
    finally show ?thesis using r by simp
  qed          
qed

lemma mk_subst_domain_distinct: "distinct (map fst (mk_subst_domain \<sigma>))"
  unfolding mk_subst_domain_def Let_def distinct_map 
  by (rule conjI[OF distinct_filter], auto simp: distinct_map inj_on_def)

(* TODO: perhaps generalize all mk_subst things to arbitrary functions 
  which are represented as finitely many key-value pairs *)
definition is_renaming_impl :: "('f,'v) substL \<Rightarrow> bool" where
  "is_renaming_impl \<sigma> \<equiv>
    let \<sigma>' = map snd (mk_subst_domain \<sigma>) in
    (\<forall> t \<in> set \<sigma>'. is_Var t) \<and> distinct \<sigma>'"

lemma is_renaming_impl [simp]:
  "is_renaming_impl \<sigma> = is_renaming (mk_subst Var \<sigma>)" (is "?l = ?r")
proof -
  let ?\<sigma> = "mk_subst Var \<sigma>"
  let ?d = "mk_subst_domain \<sigma>"
  let ?m = "map snd ?d"
  let ?k = "map fst ?d"
  have "?l = ((\<forall> t \<in> set ?m. is_Var t) \<and> distinct ?m)" unfolding is_renaming_impl_def Let_def by auto
  also have "(\<forall> t \<in> set ?m. is_Var t) = (\<forall> x. is_Var (?\<sigma> x))" 
    by (force simp: mk_subst_domain subst_domain_def)
  also have "distinct ?m = inj_on ?\<sigma> (subst_domain ?\<sigma>)" 
  proof
    assume inj: "inj_on ?\<sigma> (subst_domain ?\<sigma>)"
    show "distinct ?m" unfolding distinct_conv_nth 
    proof (intro allI impI)
      fix i j
      assume i: "i < length ?m" and j: "j < length ?m" and ij: "i \<noteq> j"
      obtain x t where di: "?d ! i = (x,t)" by (cases "?d ! i", auto)
      obtain y s where dj: "?d ! j = (y,s)" by (cases "?d ! j", auto)
      from di i have mi: "?m ! i = t" and ki: "?k ! i = x" by auto
      from dj j have mj: "?m ! j = s" and kj: "?k ! j = y" by auto
      from di i have xt: "(x,t) \<in> set ?d" unfolding set_conv_nth by force
      from dj j have ys: "(y,s) \<in> set ?d" unfolding set_conv_nth by force
      from xt ys have d: "x \<in> subst_domain ?\<sigma>" "y \<in> subst_domain ?\<sigma>" unfolding mk_subst_domain by auto
      have dist: "distinct ?k" by (rule mk_subst_domain_distinct)
      from ij i j have xy: "x \<noteq> y" unfolding ki[symmetric] kj[symmetric] 
        using dist[unfolded distinct_conv_nth] by auto
      from xt ys have m: "?\<sigma> x = t" "?\<sigma> y = s" unfolding mk_subst_domain by auto
      from inj[unfolded inj_on_def, rule_format, OF d]
      show "?m ! i \<noteq> ?m ! j" unfolding m mi mj using xy by auto
    qed
  next      
    assume dist: "distinct ?m"
    show "inj_on ?\<sigma> (subst_domain ?\<sigma>)" unfolding inj_on_def
    proof (intro ballI impI)
      fix x y
      assume x: "x \<in> subst_domain ?\<sigma>" and y: "y \<in> subst_domain ?\<sigma>" 
        and id: "?\<sigma> x = ?\<sigma> y" 
      from x y have x: "(x,?\<sigma> x) \<in> set ?d" and y: "(y,?\<sigma> y) \<in> set ?d"
        unfolding mk_subst_domain by auto
      from x obtain i where di: "?d ! i = (x,?\<sigma> x)" and i: "i < length ?d" unfolding set_conv_nth by auto
      from y obtain j where dj: "?d ! j = (y,?\<sigma> y)" and j: "j < length ?d" unfolding set_conv_nth by auto
      from di i have mi: "?m ! i = ?\<sigma> x" by simp
      from dj j have mj: "?m ! j = ?\<sigma> x" unfolding id by simp
      from mi mj have id: "?m ! i = ?m ! j" by simp
      from dist[unfolded distinct_conv_nth] i j id have id: "i = j" by auto
      with di dj
      show "x = y" by auto
    qed
  qed
  finally
  show ?thesis unfolding is_renaming_def by simp
qed

definition is_inverse_renaming_impl :: "('f, 'v) substL \<Rightarrow> ('f, 'v) substL" where
  "is_inverse_renaming_impl \<sigma> \<equiv>
    let \<sigma>' = mk_subst_domain \<sigma> in
    map (\<lambda> (x, y). (the_Var y, Var x)) \<sigma>'"

lemma is_inverse_renaming_impl [simp]:
  fixes \<sigma> :: "('f, 'v) substL"
  assumes var: "is_renaming (mk_subst Var \<sigma>)"
  shows "mk_subst Var (is_inverse_renaming_impl \<sigma>) = is_inverse_renaming (mk_subst Var \<sigma>)" (is "?l = ?r")
proof (rule ext)
  fix x
  let ?\<sigma> = "mk_subst Var \<sigma>"
  let ?\<sigma>' = "mk_subst_domain \<sigma>"
  let ?m = "map (\<lambda> (x, y). (the_Var y, Var x :: ('f, 'v) term)) ?\<sigma>'"
  let ?ran = "subst_range ?\<sigma>"
  note d = is_inverse_renaming_impl_def is_inverse_renaming_def
  {
    fix t
    assume "(x,t) \<in> set ?m" 
    then obtain u z where id: "(x,t) = (the_Var u,Var z)" and mem: "(z,u) \<in> set ?\<sigma>'" by auto
    from var[unfolded is_renaming_def] mem obtain zz where u: "u = Var zz" 
      unfolding mk_subst_domain by auto
    from id[unfolded u] have id: "zz = x" "t = Var z" by auto
    with mem u have "(z,Var x) \<in> set ?\<sigma>'" by auto
    then have "?\<sigma> z = Var x" "z \<in> subst_domain ?\<sigma>" unfolding mk_subst_domain by auto
    with id have "\<exists> z. t = Var z \<and> ?\<sigma> z = Var x \<and> z \<in> subst_domain ?\<sigma>" by auto
  } note one = this
  have "?l x = mk_subst Var ?m x" unfolding d by simp
  also have "... = ?r x" 
  proof (cases "Var x \<in> ?ran")
    case False
    {
      fix t
      assume "(x,t) \<in> set ?m"
      from one[OF this] obtain z where t: "t = Var z" and z: "?\<sigma> z = Var x" 
        and dom: "z \<in> subst_domain ?\<sigma>" by auto
      from z dom False have False by force
    }
    from this[OF map_of_SomeD[of ?m x]] have look: "map_of ?m x = None" 
      by (cases "map_of ?m x", auto)    
    then have "mk_subst Var ?m x = Var x" unfolding mk_subst_def by auto
    also have "... = ?r x" using False unfolding d by simp
    finally show ?thesis .
  next
    case True
    then obtain y where y: "y \<in> subst_domain ?\<sigma>" and x: "?\<sigma> y = Var x" by auto
    then have "(y,Var x) \<in> set ?\<sigma>'" unfolding mk_subst_domain by auto
    then have "(x,Var y) \<in> set ?m" by force
    then obtain u where look: "map_of ?m x = Some u" using map_of_eq_None_iff[of ?m x]
      by (cases "map_of ?m x", force+)
    from map_of_SomeD[OF this] have xu: "(x,u) \<in> set ?m" by auto
    from one[OF this] obtain z where u: "u = Var z" and z: "?\<sigma> z = Var x" and dom: "z \<in> subst_domain ?\<sigma>" by auto
    have "mk_subst Var ?m x = Var z" unfolding mk_subst_def look u by simp
    also have "... = ?r x" using is_renaming_inverse_domain[OF var dom] z by auto
    finally show ?thesis .
  qed
  finally show "?l x = ?r x" .
qed  

definition
  mk_subst_case :: "'v list \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) substL \<Rightarrow> ('f, 'v) substL"
  where
    "mk_subst_case xs \<sigma> \<tau> = subst_compose_impl (map (\<lambda> x. (x, \<sigma> x)) xs) \<tau>"

lemma mk_subst_case [simp]:
  "mk_subst Var (mk_subst_case xs \<sigma> \<tau>) =
    (\<lambda> x. if x \<in> set xs then \<sigma> x \<cdot> mk_subst Var \<tau> else mk_subst Var \<tau> x)" 
proof -
  let ?m = "map (\<lambda> x. (x, \<sigma> x)) xs"
  have id: "mk_subst Var ?m = (\<lambda> x. if x \<in> set xs then \<sigma> x else Var x)" (is "?l = ?r")
  proof (rule ext)
    fix x
    show "?l x = ?r x"
    proof (cases "x \<in> set xs")
      case True
      then have "(x,\<sigma> x) \<in> set ?m" by auto
      with map_of_eq_None_iff[of ?m x] obtain u where look: "map_of ?m x = Some u" by auto
      from map_of_SomeD[OF look] have u: "u = \<sigma> x" by auto
      show ?thesis unfolding mk_subst_def look u using True by auto
    next
      case False
      with map_of_SomeD[of ?m x]
      have look: "map_of ?m x = None" by (cases "map_of ?m x", auto)
      show ?thesis unfolding mk_subst_def look using False by auto
    qed
  qed
  show ?thesis unfolding mk_subst_case_def subst_compose_impl id 
    unfolding subst_compose_def by auto
qed

end