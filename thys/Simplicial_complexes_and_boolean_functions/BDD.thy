
theory BDD
  imports
    Evasive
    ROBDD.Level_Collapse
    ListLexorder
begin

section\<open>Executably converting Simplicial Complexes to BDDs\<close>
text\<open>We already know how to convert a simplicial complex to a boolean function, and that to a BDT.
We could trivially convert convert boolean functions to BDDs the same way they are converted to BDTs,
but the conversion to BDTs necessarily takes an amount of steps exponential in the number of variables (vertices).
The following method avoids this exponential method.\<close>
text\<open>This theory does not include a proof on the run-time complexity of the conversion.\<close>
(* It is still unclear to me whether this whole thing was necessary *)

text \<open>The basic idea is that each vertex in a simplicial complex corresponds to one
  @{term True} line in the truth table of the inducing Boolean function.
This is captured by the following definition, which is part of the correctness assumptions of the final theorem.\<close>
definition bf_from_sc :: "nat set set => (bool vec \<Rightarrow> bool)"
  where "bf_from_sc K \<equiv> (\<lambda>v. {i. i < dim_vec v \<and> \<not> (vec_index v i)} \<in> K)"

lemma bf_from_sc:
  assumes sc: "simplicial_complex.simplicial_complex n K"
  shows "simplicial_complex_induced_by_monotone_boolean_function n (bf_from_sc K) = K"
  unfolding bf_from_sc_def simplicial_complex_induced_by_monotone_boolean_function_def
  using sc
  unfolding simplicial_complex.simplicial_complex_def
  unfolding simplicial_complex.simplices_def
  unfolding ceros_of_boolean_input_def
  by auto (metis ceros_of_boolean_input_def dim_vec sc
      simplicial_complex.ceros_of_boolean_input_in_set simplicial_complex.simplicial_complex_def)

definition boolfunc_from_sc :: "nat => nat set set \<Rightarrow> nat boolfunc"
  where "boolfunc_from_sc n K \<equiv> \<lambda>p. {i. i < n \<and> \<not> p i} \<in> K"

text\<open>The conversion proven correct in two major steps:
\begin{itemize}
\item Prove that we can convert the list form of simplicial complexes to boolean functions instead of the set form (@{text boolfunc_from_sc_list})
\item Prove that we can convert the list form of simplicial complexes to BDDs (@{text boolfunc_bdd_from_sc_list})
\end{itemize}
\<close>

definition "sc_threshold_2_3 \<equiv> {{},{0::nat},{1},{2},{3},{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}}"

text\<open>Example: The truth table (as separate lemmas) for @{const sc_threshold_2_3}:\<close>
lemma hlp1: "{i. i < 4 \<and> \<not> (f(0 := a0, 1 := a1, 2 := a2, 3 := a3)) i} =
  (if a0 then {} else {0::nat})
\<union> (if a1 then {} else {1})
\<union> (if a2 then {} else {2})
\<union> (if a3 then {} else {3})"
  by auto

lemma sc_threshold_2_3_ffff:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a (0:=False,1:=False,2:=False,3:=False)) = False"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def
  by simp (smt (z3) Suc_eq_numeral insert_absorb insert_commute insert_ident
      insert_not_empty numeral_2_eq_2 singleton_inject zero_neq_numeral)

lemma sc_threshold_2_3_ffft:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=False,2:=False,3:=True)) = False"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def
  by simp (smt (z3) Suc_eq_numeral insertI1 insert_absorb insert_commute
      insert_ident insert_not_empty numeral_2_eq_2 singleton_inject zero_neq_numeral)

lemma sc_threshold_2_3_fftf:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=False,2:=True,3:=False)) = False"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def
  by simp (smt (z3) insertI1 insert_iff numeral_1_eq_Suc_0
      numeral_2_eq_2 numeral_eq_iff semiring_norm(86) singleton_iff zero_neq_numeral)

lemma sc_threshold_2_3_ftff:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=True,2:=False,3:=False)) = False"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def
  by simp (smt (verit, ccfv_SIG) insert_absorb insert_iff insert_not_empty
      numeral_eq_iff semiring_norm(89) zero_neq_numeral)

lemma sc_threshold_2_3_tfff:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=False,2:=False,3:=False)) = False"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def
  by simp (smt (z3) eval_nat_numeral(3) insertI1 insert_commute insert_iff
      n_not_Suc_n numeral_1_eq_Suc_0 numeral_2_eq_2
      numeral_eq_iff singletonD verit_eq_simplify(12))

lemma sc_threshold_2_3_fftt:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=False,2:=True,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_ftft:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=True,2:=False,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_fttf:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=True,2:=True,3:=False)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_fttt:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=False,1:=True,2:=True,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_tfft:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=False,2:=False,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_tftf:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=False,2:=True,3:=False)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_tftt:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=False,2:=True,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_ttff:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=True,2:=False,3:=False)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_ttft:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=True,2:=False,3:=True)) = True"
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_tttf:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=True,2:=True,3:=False)) = True "
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma sc_threshold_2_3_tttt:
  "boolfunc_from_sc 4 sc_threshold_2_3 (a(0:=True,1:=True,2:=True,3:=True)) = True "
  unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma "boolfunc_from_sc n UNIV = bf_True"
  unfolding boolfunc_from_sc_def by simp

lemma "boolfunc_from_sc n {} = bf_False"
  unfolding boolfunc_from_sc_def by simp

text\<open>This may seem like an extra step, but effectively, it means:
  require that all the atoms outside the vertex are true,
  but don't care about what's in the vertex.\<close>

lemma boolfunc_from_sc_lazy:
  "simplicial_complex.simplicial_complex n K
    \<Longrightarrow> boolfunc_from_sc n K = (\<lambda>p. Pow {i. i < n \<and> \<not> p i} \<subseteq> K)"
  unfolding simplicial_complex.simplicial_complex_def boolfunc_from_sc_def
  by auto (* wow *)

primrec boolfunc_from_vertex_list :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "boolfunc_from_vertex_list n [] = bf_True" |
  "boolfunc_from_vertex_list n (f#fs) =
      bf_and (boolfunc_from_vertex_list n fs) (if f \<in> set n then bf_True else bf_lit f)"

lemma boolfunc_from_vertex_list_Cons:
  "boolfunc_from_vertex_list (a # as) lUNIV =
    (\<lambda>v. (boolfunc_from_vertex_list as lUNIV) (v(a:=True)))"
  by (induction lUNIV; simp add: bf_lit_def)

lemma boolfunc_from_vertex_list_Empty:
  "boolfunc_from_vertex_list [] lUNIV = Ball (set lUNIV)"
  by(induction lUNIV) (auto simp add: bf_lit_def)

lemma boolfunc_from_vertex_list:
  "set lUNIV = {..<n} \<Longrightarrow> boolfunc_from_vertex_list a lUNIV = (\<lambda>p. {i. i < n \<and> \<not> p i} \<subseteq> set a)"
  by (induction a; fastforce
        simp add: boolfunc_from_vertex_list_Empty boolfunc_from_vertex_list_Cons)

primrec boolfunc_from_sc_list :: "nat list \<Rightarrow> nat list list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool"
 where
   "boolfunc_from_sc_list lUNIV [] = bf_False" |
   "boolfunc_from_sc_list lUNIV (l#L) =
      bf_or (boolfunc_from_sc_list lUNIV L) (boolfunc_from_vertex_list l lUNIV)"

lemma boolfunc_from_sc_un:
  "boolfunc_from_sc n (a\<union>b) = bf_or (boolfunc_from_sc n a) (boolfunc_from_sc n b)"
  unfolding boolfunc_from_sc_def unfolding bf_or_def bf_ite_def by force

lemma bf_ite_const[simp]: "bf_ite bf_True a b = a" "bf_ite bf_False a b = b"
  by (simp_all)

lemma Pow_subset_Pow: "Pow a \<subseteq> Pow b = (a \<subseteq> b)"
  by blast

lemma boolfunc_from_sc_list_concat:
  "boolfunc_from_sc_list lUNIV (a @ b) =
      bf_or (boolfunc_from_sc_list lUNIV a) (boolfunc_from_sc_list lUNIV b)"
  by (induction a; auto)

lemma boolfunc_from_sc_list_existing_useless:
  "a \<in> set as \<Longrightarrow> boolfunc_from_sc_list l (a # as) = boolfunc_from_sc_list l as"
proof(induction as)
  case (Cons a1s as) then show ?case by (cases "a1s = a"; simp) metis
qed simp

primrec remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "remove a [] = []" |
  "remove a (a1 # as) = (if a = a1 then [] else [a1]) @ remove a as"

lemma set_remove[simp]: "set (remove a as) = set as - {a}"
  by(induction as; auto)

lemma remove_concat[simp]: "remove a (a1 @ a2) = remove a a1 @ remove a a2"
  by(induction a1; simp)

lemma boolfunc_from_sc_list_dedup1:
  "boolfunc_from_sc_list l (a # as) = boolfunc_from_sc_list l (a # remove a as)"
proof(induction as)
  case (Cons a1s as) then show ?case by(cases "a1s = a"; simp) metis
qed simp

lemma boolfunc_from_sc_list_reorder:
  "set a = set b \<Longrightarrow> boolfunc_from_sc_list l a = boolfunc_from_sc_list l b"
proof(induction a arbitrary: b)
next
  case (Cons a1 a2)
  then obtain b1 b2 where  b: "b = b1 @ a1 # b2" by (metis list.set_intros(1) split_list)
  have cons_concat: "\<And>a as. a # as = [a] @ as" by simp
  have bb: "boolfunc_from_sc_list l b =
      bf_or (boolfunc_from_vertex_list a1 l)
            (bf_or (boolfunc_from_sc_list l b1) (boolfunc_from_sc_list l b2))"
    apply(subst b)
    apply(subst boolfunc_from_sc_list_concat)
    apply(subst cons_concat)
    apply(subst boolfunc_from_sc_list_concat)
    apply(auto)
    done
  have bbb: "boolfunc_from_sc_list l b = boolfunc_from_sc_list l (a1 # (remove a1 (b1 @ b2)))"
    unfolding bb boolfunc_from_sc_list_dedup1[symmetric]
    by (auto simp add: boolfunc_from_sc_list_concat)
  show ?case proof(cases "a1 \<in> set a2")
    case True
    then show ?thesis using Cons by (metis insert_absorb list.set(2))
  next
    case False
    then have a2: "set a2 = set (remove a1 (b1 @ b2))"
      using Cons.prems b by fastforce
    show ?thesis using  Cons.IH[OF a2] bbb by simp
  qed
qed simp

lemma boolfunc_from_sc_list:
  "set lUNIV = {..<n::nat}
    \<Longrightarrow> simplicial_complex.simplicial_complex n (set ` set L)
      \<Longrightarrow> boolfunc_from_sc_list lUNIV L = boolfunc_from_sc n (set ` set L)"
proof -
  assume lUNIV: "set lUNIV = {..<n::nat}"
  assume sc: "simplicial_complex.simplicial_complex n (set ` set L)"
  define sorted where "sorted \<equiv> sorted_wrt (\<lambda>a b :: nat list. card (set b) \<le> card (set a))"
  (* wlog, assume L is sorted. the price for that was paid in boolfunc_from_sc_list_reorder *)
  have i: "sorted L
            \<Longrightarrow> simplicial_complex.simplicial_complex n (set ` set L)
            \<Longrightarrow> boolfunc_from_sc_list lUNIV L = boolfunc_from_sc n (set ` set L)" for L
  proof(induction L)
    case Nil
    show ?case by (simp add: boolfunc_from_sc_def)
  next
    case (Cons a L)
    from Cons.prems(2) have p: "Pow (set a) \<subseteq> (set ` set (a # L))"
      unfolding simplicial_complex.simplicial_complex_def by simp
    hence pun: "insert (set a) (set ` set L) = Pow (set a) \<union> (set ` set  L)" by auto
    from p and Cons.prems(2)
    have sp: "simplicial_complex.simplicial_complex n (Pow (set a))"
      by (meson PowD Pow_subset_Pow simplicial_complex.simplicial_complex_def subsetD)
    have bfSing: "boolfunc_from_sc_list lUNIV [a] = boolfunc_from_sc n (Pow (set a))"
      unfolding boolfunc_from_sc_lazy [OF sp]
      by (simp add: Pow_subset_Pow boolfunc_from_vertex_list [OF lUNIV])
    have bflCons: "boolfunc_from_sc_list lUNIV (a # L) =
      bf_or (boolfunc_from_sc_list lUNIV [a]) (boolfunc_from_sc_list lUNIV L)"
      unfolding boolfunc_from_sc_list.simps(2) [of _ a L] by auto
    from Cons.prems have "simplicial_complex.simplicial_complex n (set ` set L)"
      unfolding simplicial_complex.simplicial_complex_def sorted_def
      by simp (metis List.finite_set PowD card_seteq insert_image subset_insert)
    from Cons.IH[OF _ this] Cons.prems(1)
    have "boolfunc_from_sc_list lUNIV L = boolfunc_from_sc n (set ` set L)"
      unfolding sorted_def by simp
    thus ?case
      apply(subst bflCons)
      apply(simp del: boolfunc_from_sc_list.simps)
      apply(subst pun)
      apply(subst boolfunc_from_sc_un)
      apply(subst bfSing)
      apply(simp)
      done
  qed
  define sort where "sort \<equiv> rev (sort_key (\<lambda>l. card (set l)) L)"
  have sc: "simplicial_complex.simplicial_complex n (set ` set sort)"
    unfolding sort_def using sc by simp
  have sorted: "sorted sort"
    by(simp add: sorted_def sort_def sorted_wrt_rev) (metis sorted_map sorted_sort_key)
  have set: "set sort = set L" unfolding sort_def by simp
  from boolfunc_from_sc_list_reorder[OF set] i[OF sorted sc] set
  show ?thesis by presburger
qed

lemma boolfunc_from_sc_alt: "boolfunc_from_sc n K = vec_to_boolfunc n (bf_from_sc K)"
  unfolding boolfunc_from_sc_def vec_to_boolfunc_def bf_from_sc_def
  unfolding dim_vec by(fastforce intro!: eqelem_imp_iff)

primrec bdd_from_vertex_list :: "nat list \<Rightarrow> nat list \<Rightarrow> bddi \<Rightarrow> (nat \<times> bddi) Heap"
  where
    "bdd_from_vertex_list n [] s = tci s" |
    "bdd_from_vertex_list n (f#fs) s = do {
      (f, s) \<leftarrow> if f \<in> set n then tci s else litci f s;
      (fs, s) \<leftarrow> bdd_from_vertex_list n fs s;
    andci fs f s
}"

(* You'd guess that andci is commutative, and thus the argument order doesn't matter.
   You'd be wrong. The automation very much doesn't know about that. *)

primrec bdd_from_sc_list :: "nat list \<Rightarrow> nat list list \<Rightarrow> bddi \<Rightarrow> (nat \<times> bddi) Heap"
  where
    "bdd_from_sc_list lUNIV [] s = fci s" |
    "bdd_from_sc_list lUNIV (l#L) s = do {
      (l, s) \<leftarrow> bdd_from_vertex_list l lUNIV s;
      (L, s) \<leftarrow> bdd_from_sc_list lUNIV L s;
      orci L l s
}"

definition "nat_list_from_vertex v \<equiv> sorted_list_of_set v"

definition "nat_list_from_sc K \<equiv> sorted_list_of_list_set (nat_list_from_vertex ` K)"

definition "ex_2_3 \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3] (nat_list_from_sc sc_threshold_2_3) s;
  graphifyci ''threshold_two_three'' ex s
}"

lemma nat_list_from_vertex:
  assumes "finite l"
  shows "set (nat_list_from_vertex l) = {i . i \<in> l}"
  unfolding nat_list_from_vertex_def sorted_list_of_set_def
  by auto (metis assms set_sorted_list_of_set sorted_list_of_set_def)+

lemma
  finite_sorted_list_of_set:
  assumes "finite L"
  shows "finite (sorted_list_of_set ` L)"
    using finite_imageI [OF assms, of sorted_list_of_set] .

lemma nat_list_from_sc:
  assumes L: "finite L"
  and l: "\<forall>l\<in>L. finite l"
  shows "set ` set (nat_list_from_sc (L :: nat set set)) = {{i . i \<in> l} | l. l \<in>  L}"
  unfolding nat_list_from_sc_def
  unfolding nat_list_from_vertex_def
  unfolding set_sorted_list_of_list_set [OF finite_sorted_list_of_set [OF L]]
proof (safe)
  fix x :: "nat set"
  assume xl: "x \<in> L"
  hence fx: "finite x" using l by simp
  show exl: "\<exists>l. set (sorted_list_of_set x) = {i. i \<in> l} \<and> l \<in> L"
    by (rule exI [of _ x], auto simp add: xl fx)
  show "{i. i \<in> x} \<in> set ` sorted_list_of_set ` L"
    by (metis Collect_mem_eq exl fx image_iff set_sorted_list_of_set)
qed

(* hommm. seeing is believing. how to execute? *)

definition "ex_false \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3] (nat_list_from_sc {}) s;
  graphifyci ''false'' ex s
}"

definition "ex_true \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3]
      (nat_list_from_sc
      {{},{0},{1},{2},{3},
       {0,1},{0,2},{0,3},{1,2},{1,3},{2,3},
       {0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3}}) s;
  graphifyci ''true'' ex s
}"

definition "another_ex \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3]
      (nat_list_from_sc
        {{},{0},{1},{2},{3},
         {0,1},{0,2},{0,3},{1,2},{1,3},{2,3},
         {0,1,2},{0,1,3},{0,2,3},{1,2,3}}) s;
  graphifyci ''another_ex'' ex s
}"

definition "one_another_ex \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3]
            (nat_list_from_sc
            {{},{0},{1},{2},{3},
             {0,1},{0,2},{0,3},{1,2},{1,3},{2,3},
             {0,1,2},{0,1,3},{1,2,3}}) s;
  graphifyci ''one_another_ex'' ex s
}"


lemma bf_ite_direct[simp]: "bf_ite i bf_True bf_False = i" by simp

lemma andciI: "node_relator (tb, tc) rp \<Longrightarrow> node_relator (eb, ec) rp \<Longrightarrow> rq \<subseteq> rp \<Longrightarrow>
      <bdd_relator rp s> andci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_and tb eb,r) rq) s'>"
  by sep_auto

lemma bdd_from_vertex_list[sep_heap_rules]:
  shows "<bdd_relator rp s>
    bdd_from_vertex_list n l s
  <\<lambda>(r,s'). bdd_relator (insert (boolfunc_from_vertex_list n l, r) rp) s'>"
proof(induction l arbitrary: rp s)
  case Nil then show ?case by (sep_auto)
next
  case (Cons a l)
  show ?case proof(cases "a \<in> set n")
    case True
    show ?thesis
      apply(simp only: bdd_from_vertex_list.simps list.map
          boolfunc_from_vertex_list.simps True if_True)
      apply(sep_auto simp only:)
       apply(rule Cons.IH)
      apply(clarsimp simp del: bf_ite_def)
      apply(sep_auto)
      done
  next
    case False
    show ?thesis
      apply(simp only: bdd_from_vertex_list.simps list.map
          boolfunc_from_vertex_list.simps False if_False)
      apply(sep_auto simp only:)
       apply(rule Cons.IH)
      apply(sep_auto simp del: bf_ite_def bf_and_def)
    done
  qed
qed

lemma boolfunc_bdd_from_sc_list:
  shows "<bdd_relator rp s>
    bdd_from_sc_list lUNIV K s
  <\<lambda>(r,s'). bdd_relator (insert (boolfunc_from_sc_list lUNIV K, r) rp) s'>"
proof(induction K arbitrary: rp s)
  case Nil
  then show ?case by sep_auto
next
  case (Cons a K)
  show ?case by(sep_auto heap add: Cons.IH simp del: bf_ite_def bf_or_def)
qed

lemma map_map_idI: "(\<And>x. x \<in> \<Union>(set ` set l) \<Longrightarrow> f x = x) \<Longrightarrow> map (map f) l = l"
  by(induct l; simp; meson map_idI)

definition
  "bdd_from_sc K n \<equiv> bdd_from_sc_list (nat_list_from_vertex {..<n}) (nat_list_from_sc K)"

theorem bdd_from_sc:
  assumes "simplicial_complex.simplicial_complex n (K :: nat set set)"
  shows "<bdd_relator rp s>
    bdd_from_sc K n s
  <\<lambda>(r,s'). bdd_relator (insert (vec_to_boolfunc n (bf_from_sc K), r) rp) s'>"
proof -
  have fK: "finite K"
    using simplicial_complex.finite_simplicial_complex [OF assms] .
  have fv: "\<forall>v\<in>K. finite v"
    using simplicial_complex.finite_simplices [OF assms] ..
  define lUNIV where lUNIV_def: "lUNIV = nat_list_from_vertex {..<n}"
  hence set_lUNIV: "set lUNIV = {..<n}"
    unfolding nat_list_from_vertex_def
    using sorted_list_of_set(1) [OF finite_lessThan [of n]] by simp
  define Klist where "Klist \<equiv> (nat_list_from_sc K)"
  have Klist_set: "set ` set Klist = K"
    using nat_list_from_sc [OF fK fv]
    unfolding Klist_def nat_list_from_sc_def nat_list_from_vertex_def by simp
  have Klist_map: "Klist = nat_list_from_sc K"
    unfolding Klist_def ..
  have sc_Klist: "simplicial_complex.simplicial_complex n (set ` set Klist)"
    unfolding Klist_set using assms .
  show ?thesis
    apply (insert boolfunc_bdd_from_sc_list[of rp s lUNIV Klist])
    unfolding bdd_from_sc_def unfolding Klist_def [symmetric]
    unfolding lUNIV_def [symmetric]
    unfolding boolfunc_from_sc_list [OF set_lUNIV sc_Klist]
    unfolding Klist_set
    unfolding boolfunc_from_sc_alt by simp
qed

code_identifier
  code_module Product_Type \<rightharpoonup> (SML) IBDD
    and (OCaml) IBDD and (Haskell) IBDD
  | code_module Typerep \<rightharpoonup> (SML) IBDD
    and (OCaml) IBDD and (Haskell) IBDD
  | code_module String \<rightharpoonup> (SML) IBDD
    and (OCaml) IBDD and (Haskell) IBDD

export_code open bdd_from_sc ex_2_3 ex_false ex_true another_ex one_another_ex
  in Haskell module_name IBDD file BDD

export_code bdd_from_sc ex_2_3 (* I guess this means its actually executable? *)
  in SML module_name IBDD file SMLBDD

end
