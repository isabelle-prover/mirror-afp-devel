section \<open>Deciding RPO-constraints is NP-hard\<close>

text \<open>We show that for a given an RPO it is NP-hard to decide whether two terms are in relation,
  following a proof in \<^cite>\<open>"RPO_NPC"\<close>.\<close>

theory RPO_NP_Hard
  imports 
    Multiset_Ordering_NP_Hard
    Weighted_Path_Order.RPO
begin

subsection \<open>Definition of the Encoding\<close>

datatype FSyms = A | F | G | H | U (* unsigned *) | P (* positive sign *) | N (* negative sign *)

text \<open>We slightly deviate from the paper encoding, since we add the three constants
  @{const U}, @{const P}, @{const N} in order to be able to easily convert an encoded term
  back to the multiset-element.\<close>

fun ms_elem_to_term :: "'a cnf \<Rightarrow> 'a ms_elem \<Rightarrow> (FSyms, 'a + nat)term" where
  (* y_i in the paper *)
  "ms_elem_to_term cnf (Inr i) = Var (Inr i)"
| (* t_x in the paper *)
  "ms_elem_to_term cnf (Inl (x, Unsigned)) = Fun F (Var (Inl x) # Fun U [] # 
        map (\<lambda> _. Fun A []) cnf)" 
  (* t+_x in the paper *)
| "ms_elem_to_term cnf (Inl (x, Positive)) = Fun F (Var (Inl x) # Fun P [] # 
        map (\<lambda> i. if (x,True) \<in> set (cnf ! i) then Var (Inr i) else Fun A []) [0 ..< length cnf])"
  (* t-_x in the paper *)
| "ms_elem_to_term cnf (Inl (x, Negative)) = Fun F (Var (Inl x) # Fun N [] # 
        map (\<lambda> i. if (x,False) \<in> set (cnf ! i) then Var (Inr i) else Fun A []) [0 ..< length cnf])"

definition term_lists_of_cnf :: "'a cnf \<Rightarrow> (FSyms, 'a + nat)term list \<times> (FSyms, 'a + nat)term list" where
  "term_lists_of_cnf cnf = (case multiset_problem_of_cnf cnf of
       (as, bs, S, NS) \<Rightarrow>
       (map (ms_elem_to_term cnf) as, map (ms_elem_to_term cnf) bs))" 

definition rpo_constraint_of_cnf :: "'a cnf \<Rightarrow> (_,_)term \<times> (_,_)term" where
  "rpo_constraint_of_cnf cnf = (case term_lists_of_cnf cnf of
       (as, bs) \<Rightarrow> (Fun G as, Fun H bs))" 

text \<open>An RPO instance where all symbols are equivalent in precedence and all symbols have
  multiset-status.\<close>
interpretation trivial_rpo: rpo_with_assms "\<lambda> f g. (False, True)" "\<lambda> f. True" "\<lambda> _. Mul" 0
  by (unfold_locales, auto)

subsection \<open>Soundness of the Encoding\<close>

fun term_to_ms_elem :: "(FSyms, 'a + nat)term \<Rightarrow> 'a ms_elem" where
  "term_to_ms_elem (Var (Inr i)) = Inr i" 
| "term_to_ms_elem (Fun F (Var (Inl x) # Fun U _ # ts)) = Inl (x, Unsigned)" 
| "term_to_ms_elem (Fun F (Var (Inl x) # Fun P _ # ts)) = Inl (x, Positive)" 
| "term_to_ms_elem (Fun F (Var (Inl x) # Fun N _ # ts)) = Inl (x, Negative)" 
| "term_to_ms_elem _ = undefined" 

lemma term_to_ms_elem_ms_elem_to_term[simp]: "term_to_ms_elem (ms_elem_to_term cnf x) = x" 
  apply (cases x)
  subgoal for a by (cases a, cases "snd a", auto)
  by auto

lemma (in rpo_with_assms) rpo_vars_term: "rpo_s s t \<or> rpo_ns s t \<Longrightarrow> vars_term s \<supseteq> vars_term t" 
proof (induct s t rule: rpo.induct[of _ prc prl c n], force, force)
  case (3 f ss y)
  thus ?case
    by (smt (verit, best) fst_conv rpo.simps(3) snd_conv subset_eq term.set_intros(4))
next
  case (4 f ss g ts)
  show ?case
  proof (cases "\<exists>s\<in>set ss. rpo_ns s (Fun g ts)")
    case True
    from 4(1) True show ?thesis by auto
  next
    case False
    obtain ps pns where prc: "prc (f, length ss) (g, length ts) = (ps, pns)" by force
    from False have "(if (\<exists>s\<in>set ss. rpo_ns s (Fun g ts)) then b else e) = e" for b e :: "bool \<times> bool" by simp
    note res = 4(5)[unfolded rpo.simps this prc Let_def split]
    from res have rel: "\<forall>t\<in>set ts. rpo_s (Fun f ss) t" by (auto split: if_splits)
    note IH = 4(2)[OF False prc[symmetric] refl]
    from rel IH show ?thesis by auto
  qed
qed


lemma term_lists_of_cnf: assumes "term_lists_of_cnf cnf = (as, bs)" 
  and non_triv: "cnf \<noteq> []" 
  shows "(\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> (mset as, mset bs) \<in> s_mul_ext (trivial_rpo.RPO_NS) (trivial_rpo.RPO_S)"
  "length (vars_of_cnf cnf) \<ge> 2 \<Longrightarrow> 
     (\<exists> \<beta>. eval_cnf \<beta> cnf) \<longleftrightarrow> (Fun G as, Fun H bs) \<in> trivial_rpo.RPO_S"
proof - 
  obtain xs ys S NS where mp: "multiset_problem_of_cnf cnf = (xs,ys,S,NS)" 
    by (cases "multiset_problem_of_cnf cnf", auto)
  from assms(1)[unfolded term_lists_of_cnf_def mp split]
  have abs: "as = map (ms_elem_to_term cnf) xs" "bs = map (ms_elem_to_term cnf) ys" by auto
  from mp[unfolded multiset_problem_of_cnf_def Let_def List.maps_def, simplified]
  have S: "S = concat (map (\<lambda>i. map (\<lambda>l. (ms_elem_of_lit l, Inr i)) (cnf ! i)) [0..<length cnf])" 
    and NS: "NS = concat (map (\<lambda>x. [(Inl (x, Positive), Inl (x, Unsigned)), (Inl (x, Negative), Inl (x, Unsigned))]) (vars_of_cnf cnf)) @ S" 
    and ys: "ys = map (\<lambda>x. Inl (x, Unsigned)) (vars_of_cnf cnf) @ map Inr [0..<length cnf]" 
    and xs: "xs = concat (map (\<lambda>x. [Inl (x, Positive), Inl (x, Negative)]) (vars_of_cnf cnf))" by auto
  show one: "(\<exists> \<beta>. eval_cnf \<beta> cnf)
     \<longleftrightarrow> (mset as, mset bs) \<in> s_mul_ext (trivial_rpo.RPO_NS) (trivial_rpo.RPO_S)" 
    unfolding multiset_problem_of_cnf(2)[OF mp non_triv]
  proof
    assume "(mset xs, mset ys) \<in> s_mul_ext (set NS) (set S)" 
    hence mem: "(xs, ys) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext (set NS) (set S)}" by simp
    have "(as, bs) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S}" 
      unfolding abs 
    proof (rule s_mul_ext_map[OF _ _ mem, of "ms_elem_to_term cnf"])
      {
        fix a b
        assume "(a,b) \<in> set S" 
        from this[unfolded S, simplified]
        obtain i x s where i: "i < length cnf" and a: "a = ms_elem_of_lit (x,s)" 
          and mem: "(x,s) \<in> set (cnf ! i)" and b: "b = Inr i" by auto
        from mem i obtain t ts where a: "ms_elem_to_term cnf a = Fun F (Var (Inl x) # t # ts)" and len: "length ts = length cnf" and tsi: "ts ! i = Var (Inr i)" 
          unfolding a by (cases s, auto)
        from len i tsi have mem: "Var (Inr i) \<in> set ts" unfolding set_conv_nth by auto
        show "(ms_elem_to_term cnf a, ms_elem_to_term cnf b) \<in> trivial_rpo.RPO_S" 
          unfolding a b by (simp add: Let_def, intro disjI2 bexI[OF _ mem], simp)
      } note S = this
      fix a b
      assume mem: "(a,b) \<in> set NS" 
      show "(ms_elem_to_term cnf a, ms_elem_to_term cnf b) \<in> trivial_rpo.RPO_NS" 
      proof (cases "(a,b) \<in> set S")
        case True
        from S[OF this] show ?thesis using trivial_rpo.RPO_S_subset_RPO_NS by fastforce
      next
        case False
        with mem[unfolded NS] obtain x s where "x \<in> set (vars_of_cnf cnf)" and 
          a: "a = Inl (x, s)" and b: "b = Inl (x, Unsigned)" and s: "s = Positive \<or> s = Negative" 
          by auto
        show ?thesis unfolding a b using s
          apply (auto intro!: all_nstri_imp_mul_nstri)
          subgoal for i by (cases i; cases "i - 1", auto intro!: all_nstri_imp_mul_nstri)
          subgoal for i by (cases i; cases "i - 1", auto intro!: all_nstri_imp_mul_nstri)
          done
      qed
    qed
    thus "(mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S" 
      unfolding abs by simp
  next
    assume "(mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S" 
    hence mem: "(as, bs) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S}" by simp
    have xsys: "xs = map term_to_ms_elem as" "ys = map term_to_ms_elem bs" unfolding abs map_map o_def
      by (rule nth_equalityI, auto)
    have "(xs, ys) \<in> {(as, bs). (mset as, mset bs) \<in> s_mul_ext (set NS) (set S)}" 
      unfolding xsys
    proof (rule s_mul_ext_map[OF _ _ mem])
      fix a b
      assume ab: "a \<in> set as" "b \<in> set bs" 
      from ab(2)[unfolded abs] obtain y where y: "y \<in> set ys" and b: "b = ms_elem_to_term cnf y" by auto
      from ab(1)[unfolded abs] obtain x where x: "x \<in> set xs" and a: "a = ms_elem_to_term cnf x" by auto
      from y[unfolded ys] obtain v i where y: "y = Inl (v, Unsigned) \<and> v \<in> set (vars_of_cnf cnf)
          \<or> y = Inr i \<and> i < length cnf" by auto
      from x[unfolded xs] obtain w s where s: "s = Positive \<or> s = Negative" and w: "w \<in> set (vars_of_cnf cnf)" 
        and x: "x = Inl (w, s)" by auto
      {
        assume y: "y = Inl (v, Unsigned)" and v: "v \<in> set (vars_of_cnf cnf)" 
        {
          assume "(a,b) \<in> trivial_rpo.RPO_NS" 
          from s this v have "(term_to_ms_elem a, term_to_ms_elem b) \<in> set NS" unfolding a b x y
            by (cases s, auto split: if_splits simp: Let_def NS)
        } note case11 = this
        {
          assume "(a,b) \<in> trivial_rpo.RPO_S" 
          hence "trivial_rpo.rpo_s a b" by simp
          from s this v have False unfolding a b x y
            by (cases, auto split: if_splits simp: Let_def, auto dest!: fst_mul_ext_imp_fst)
        } note case12 = this
        note case11 case12
      } note case1 = this
      {
        assume y: "y = Inr i" and i: "i < length cnf" 
        assume "(a,b) \<in> trivial_rpo.RPO_NS \<union> trivial_rpo.RPO_S" 
        hence "(a,b) \<in> trivial_rpo.RPO_NS"
          using trivial_rpo.RPO_S_subset_RPO_NS by blast
        from s this have "(term_to_ms_elem a, term_to_ms_elem b) \<in> set S" unfolding a b x y
          by (cases, auto split: if_splits simp: Let_def NS S, force+)
      } note case2 = this
      from case1 case2 y
      show "(a, b) \<in> trivial_rpo.RPO_S \<Longrightarrow> (term_to_ms_elem a, term_to_ms_elem b) \<in> set S" by auto
      from case1 case2 y
      show "(a, b) \<in> trivial_rpo.RPO_NS \<Longrightarrow> (term_to_ms_elem a, term_to_ms_elem b) \<in> set NS" unfolding NS by auto
    qed
    thus "(mset xs, mset ys) \<in> s_mul_ext (set NS) (set S)" by simp
  qed

  text \<open>Here the encoding for single RPO-terms is handled. We do this here and not in a separate
    lemma, since some of the properties of xs, ys, as, bs, etc. are required.\<close>
  assume len2: "length (vars_of_cnf cnf) \<ge> 2" 
  show "(\<exists> \<beta>. eval_cnf \<beta> cnf) \<longleftrightarrow> (Fun G as, Fun H bs) \<in> trivial_rpo.RPO_S" 
    unfolding one
  proof
    assume mul: "(mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S" 
    {
      fix b
      assume "b \<in> set bs" 
      hence "b \<in># mset bs" by auto
      from s_mul_ext_point[OF mul this] have "\<exists> a \<in> set as. (a,b) \<in> trivial_rpo.RPO_NS"
        using trivial_rpo.RPO_S_subset_RPO_NS by fastforce      
      hence "(Fun G as, b) \<in> trivial_rpo.RPO_S" by (cases b, auto)
    } 
    with mul show "(Fun G as, Fun H bs) \<in> trivial_rpo.RPO_S" 
      by (auto simp: mul_ext_def)
  next
    assume rpo: "(Fun G as, Fun H bs) \<in> trivial_rpo.RPO_S"
    have "\<not> (\<exists>s\<in>set as. trivial_rpo.rpo_ns s (Fun H bs))" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      then obtain a where a: "a \<in> set as" and "trivial_rpo.rpo_ns a (Fun H bs)" by auto
      with trivial_rpo.rpo_vars_term[of a "Fun H bs"] 
      have vars: "vars_term (Fun H bs) \<subseteq> vars_term a" by auto
      from a[unfolded abs xs, simplified] obtain x where "vars_term a \<inter> range Inl = {Inl x}" 
        by force
      with vars have sub: "vars_term (Fun G bs) \<inter> range Inl \<subseteq> {Inl x}" by auto
      from len2 obtain y z vs where vars: "vars_of_cnf cnf = y # z # vs" 
        by (cases "vars_of_cnf cnf"; cases "tl (vars_of_cnf cnf)", auto)
      have "distinct (vars_of_cnf cnf)" unfolding vars_of_cnf_def by auto
      with vars have yz: "y \<noteq> z" by auto
      have "{Inl y, Inl z} \<subseteq> vars_term (Fun G bs)" 
        unfolding abs ys vars by auto
      with sub yz
      show False by auto
    qed
    with rpo have "fst (mul_ext trivial_rpo.rpo_pr as bs)" by (auto split: if_splits)
    thus "(mset as, mset bs) \<in> s_mul_ext trivial_rpo.RPO_NS trivial_rpo.RPO_S" 
      by (auto simp: mul_ext_def Let_def)
  qed
qed

lemma rpo_constraint_of_cnf: assumes non_triv: "length (vars_of_cnf cnf) \<ge> 2" 
shows "(\<exists> \<beta>. eval_cnf \<beta> cnf) \<longleftrightarrow> rpo_constraint_of_cnf cnf \<in> trivial_rpo.RPO_S"
proof -
  obtain as bs where res: "term_lists_of_cnf cnf = (as,bs)" by force
  from non_triv have cnf: "cnf \<noteq> []" unfolding vars_of_cnf_def by auto
  show ?thesis unfolding rpo_constraint_of_cnf_def res split
    by (subst term_lists_of_cnf(2)[OF res cnf non_triv], auto)
qed 

subsection \<open>Size of Encoding is Quadratic\<close>

fun term_size :: "('f,'v)term \<Rightarrow> nat" where
  "term_size (Var x) = 1" 
| "term_size (Fun f ts) = 1 + sum_list (map term_size ts)" 

lemma size_of_rpo_constraint_of_cnf:
  assumes "rpo_constraint_of_cnf cnf = (s,t)" 
  and "size_cnf cnf = n" 
  shows "term_size s + term_size t \<le> 4 * n\<^sup>2 + 12 * n + 2" 
proof -
  obtain as bs S NS where mp: "multiset_problem_of_cnf cnf = (as, bs, S, NS)" 
    by (cases "multiset_problem_of_cnf cnf", auto)
  from size_of_multiset_problem_of_cnf[OF mp assms(2)]
  have las: "length as \<le> 2 * n" "length bs \<le> 2 * n" by auto
  have tl: "term_lists_of_cnf cnf = (map (ms_elem_to_term cnf) as, map (ms_elem_to_term cnf) bs)" 
    unfolding term_lists_of_cnf_def mp split by simp
  from assms(1)[unfolded rpo_constraint_of_cnf_def tl split]
  have st: "s = Fun G (map (ms_elem_to_term cnf) as)" "t = Fun H (map (ms_elem_to_term cnf) bs)" by auto
  have [simp]: "term_size (if b then Var (Inr x) :: (FSyms, 'a + nat) Term.term else Fun A []) = 1" for b x 
    by (cases b, auto)
  have len_n: "length cnf \<le> n" using assms(2) unfolding size_cnf_def by auto
  have "term_size (ms_elem_to_term cnf a) \<le> 3 + length cnf" for a
    by (cases "(cnf,a)" rule: ms_elem_to_term.cases, auto simp: o_def sum_list_triv)
  also have "\<dots> \<le> 3 + n" using len_n by auto
  finally have size_ms: "term_size (ms_elem_to_term cnf a) \<le> 3 + n" for a .
  {
    fix u
    assume "u \<in> {s,t}" 
    then obtain G cs where "cs \<in> {as, bs}" and u: "u = Fun G (map (ms_elem_to_term cnf) cs)" 
      unfolding st by auto
    hence lcs: "length cs \<le> 2 * n" using las by auto
    have "term_size u = 1 + (\<Sum>x\<leftarrow>cs. term_size (ms_elem_to_term cnf x))" unfolding u by (simp add: o_def size_list_conv_sum_list)
    also have "\<dots> \<le> 1 + (\<Sum>x\<leftarrow>cs. 3 + n)" 
      by (intro add_mono lcs le_refl sum_list_mono size_ms)
    also have "\<dots> \<le> 1 + (2 * n) * (3 + n)" unfolding sum_list_triv
      by (intro add_mono le_refl mult_mono, insert lcs, auto)
    also have "\<dots> = 2 * n^2 + 6 * n + 1" by (simp add: field_simps power2_eq_square)
    finally have "term_size u \<le> 2 * n\<^sup>2 + 6 * n + 1" .
  }
  from this[of s] this[of t]
  show "term_size s + term_size t \<le> 4 * n\<^sup>2 + 12 * n + 2" by simp
qed

subsection \<open>Check Executability\<close>

value (code) "case rpo_constraint_of_cnf [
  [(''x'',True),(''y'',False)],              \<comment> \<open>clause 0\<close>
  [(''x'',False)],                           \<comment> \<open>clause 1\<close>
  [(''y'',True),(''z'',True)],               \<comment> \<open>clause 2\<close>
  [(''x'',True),(''y'',True),(''z'',False)]] \<comment> \<open>clause 3\<close> 
   of (s,t) \<Rightarrow> (''SAT: '', trivial_rpo.rpo_s s t, ''Encoding: '', s, '' >RPO '', t)" 

hide_const (open) A F G H U P N


end