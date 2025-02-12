(*
 Title:List_Space.thy
 Author: Tetsuya Sato
*)

theory List_Space
  imports
    "HOL-Analysis.Finite_Product_Measure"
    "Source_and_Sink_Algebras_Constructions"
    "Measurable_Isomorphism"
begin

section \<open> Measurable space of finite lists \<close>

text \<open> This entry introduces a measurable space of finite lists over a measurable space. The construction is inspired from Hirata's idea on list quasi-Borel spaces [Hirata et al., ITP 2023]. First, we construct countable coproduct space of product of n spaces. Then, we trasnsfer it to list space via bijections. \<close>

subsection \<open> miscellaneous lemmas \<close>

lemma measurable_pair_assoc[measurable]:
  shows "(\<lambda>((a, b), x). (a, b, x)) \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C"
proof-
  have "(\<lambda>((a,b),x). (a,b,x)) = (\<lambda>x. ((fst (fst x)),(snd (fst x)), snd x))"
    by auto
  also have "... \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C"
    by measurable
  finally show "(\<lambda>((a, b), x). (a, b, x)) \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C".
qed

lemma measurable_pair_assoc'[measurable]:
  shows "(\<lambda>((a, b), x, l). (a, b, x, l)) \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D"
proof-
  have "(\<lambda>((a,b),x,l). (a,b,x,l)) = (\<lambda>x. ((fst (fst x)),(snd (fst x)), (fst (snd x)), (snd (snd x))))"
    by auto
  also have "... \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D"
    by measurable
  finally show "(\<lambda>((a, b), x, l). (a, b, x, l)) \<in> (A \<Otimes>\<^sub>M B) \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D \<rightarrow>\<^sub>M A \<Otimes>\<^sub>M B \<Otimes>\<^sub>M C \<Otimes>\<^sub>M D".
qed

subsection \<open> construction of list space \<close>

fun pair_to_list  :: "(nat \<times> (nat \<Rightarrow> 'a)) \<Rightarrow> 'a list" where
  Zero: "pair_to_list (0,_) = []"
| Suc: "pair_to_list (Suc n,f) = (f 0) # pair_to_list (n, \<lambda> n. f (Suc n))"

fun list_to_pair  :: "'a list \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'a))" where
  Nil: "list_to_pair [] = (0,\<lambda>_.undefined)"
| Cons: "list_to_pair (x#xs) = (Suc (fst(list_to_pair xs)), \<lambda>n. if n = 0 then x else (snd(list_to_pair xs))(n - 1))"

definition\<^marker>\<open>tag important\<close> listM :: "'a measure \<Rightarrow> 'a list measure" where
  "listM M =
    initial_source (lists (space M)) {(list_to_pair, \<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)}"

lemma space_listM:
  shows "space (listM M) = (lists (space M))"
  by (auto simp: listM_def)

lemma lists_listM[measurable]:
  shows "lists (space M) \<in> sets (listM M)"
  by (metis sets.top space_listM)

lemma comp_list_to_list:
  shows "pair_to_list (list_to_pair xs) = xs"
  by(induction xs, auto)

lemma list_to_pair_function:
  shows "list_to_pair \<in> lists (space M) \<rightarrow> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
  unfolding space_prod_initial_source space_coprod_final_sink space_listM
proof(rule funcsetI)
  fix xs
  show "xs \<in> lists (space M)\<Longrightarrow> list_to_pair xs \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)"
  proof(induction xs)
    case Nil
    thus "list_to_pair [] \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)"
      unfolding PiE_def Sigma_def by auto
  next
    case (Cons x ys)
    hence propxys: "x \<in> (space M)" "ys \<in> lists (space M)"using Cons_in_lists_iff by auto
    from local.Cons obtain n f where propnf: "((list_to_pair ys) = (n,f))" "(n\<in>(UNIV :: nat set))" "(f \<in> {..<n} \<rightarrow>\<^sub>E(space M))"
      unfolding Sigma_def by auto
    have "list_to_pair (x # ys) \<in> ({Suc n} \<times> ({..<(Suc n)} \<rightarrow>\<^sub>E(space M)))"
      using propxys propnf unfolding extensional_def PiE_def
      by(cases"n = 0",auto)
    also have "... \<subseteq> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)"
      unfolding Sigma_def by(intro subsetI, blast)
    finally show "list_to_pair (x # ys) \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)".
  qed
qed

lemma list_to_pair_measurable:
  shows "list_to_pair \<in> (listM M) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
  unfolding listM_def using list_to_pair_function
  by (metis insertI1 measurable_initial_source1)

lemma comp_pair_to_pair:
  shows "(n,f) \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E(space M)) \<Longrightarrow> (list_to_pair (pair_to_list (n,f)) = (n,f))"
proof(induct n arbitrary: f)
  case 0
  thus ?case by auto
next
  case (Suc n)
  have "(Suc n, f) \<in> {(n,f) | n f. n\<in> UNIV \<and> f \<in> {..<n} \<rightarrow>\<^sub>E(space M)}"
    using Suc.prems by blast
  hence "(n, \<lambda> n. f (Suc n)) \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)"
    by (auto simp add: Sigma_def)
  hence in1: "list_to_pair (pair_to_list (n, \<lambda> n. f (Suc n))) =(n, \<lambda> n. f (Suc n))"
    by (auto simp add: Suc.hyps)
  thus ?case by auto
qed

lemma pair_to_list_function:
  shows "pair_to_list \<in> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow> lists (space M)"
  unfolding space_prod_initial_source space_coprod_final_sink space_listM
proof
  fix x :: "(nat \<times> _)" assume "x \<in> (SIGMA n:UNIV. {..<n} \<rightarrow>\<^sub>E space M)"
  then obtain n f where x: "x = (n,f) \<and> (f \<in> {..<n} \<rightarrow>\<^sub>E space M)"
    unfolding Sigma_def by auto
  have "\<And>f. (f \<in> {..<n} \<rightarrow>\<^sub>E space M) \<Longrightarrow> pair_to_list (n,f) \<in> lists (space M)"
  proof(induction n)
    case 0
    thus ?case by auto
  next
    case (Suc n)
    hence "(f 0) \<in> space M" and "(\<lambda> n. f (Suc n))\<in> {..<n} \<rightarrow>\<^sub>E space M"
      and "\<And>f. (f \<in> {..<n} \<rightarrow>\<^sub>E space M) \<Longrightarrow> pair_to_list (n,f) \<in> lists (space M)"
      by auto
    hence "pair_to_list (Suc n, f) \<in> lists (space M)"
      using lists.Cons by auto
    thus ?case by auto
  qed
  thus"pair_to_list x \<in> lists (space M)"using x by auto
qed

proposition pair_to_list_measurable:
  shows "pair_to_list \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M (listM M)"
  unfolding listM_def using pair_to_list_function
proof(rule measurable_initial_source2)
  have "list_to_pair \<in> lists (space M) \<rightarrow> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
    by (auto simp: list_to_pair_function)
  thus"\<forall>(f, N)\<in>{(list_to_pair, (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M))}. f \<in> lists (space M) \<rightarrow> space N"
    by blast
  have "(\<lambda>x. list_to_pair (pair_to_list x)) \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
  proof(subst measurable_cong[where g ="id"])
    show "\<And>w. w \<in> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<Longrightarrow> list_to_pair (pair_to_list w) = id w"
      unfolding space_prod_initial_source space_coprod_final_sink using comp_pair_to_pair by fastforce
  qed(auto)
  thus"\<forall>(f, N)\<in>{(list_to_pair, (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M))}. (\<lambda>x. f (pair_to_list x)) \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N"
    by blast
qed

proposition measurable_iff_list_and_pair:
  shows measurable_iff_pair_to_list: "\<And> f. (f \<in> (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o pair_to_list \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    and measurable_iff_list_to_pair: "\<And> f. (f o list_to_pair \<in> (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    and measurable_iff_pair_to_list2: "\<And> f. (f \<in> N \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)) \<longleftrightarrow> (pair_to_list \<circ> f\<in> N \<rightarrow>\<^sub>M listM M \<and> f \<in> space N \<rightarrow> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M))"
    and measurable_iff_list_to_pair2: "\<And> f. (f \<in> N \<rightarrow>\<^sub>M listM M) \<longleftrightarrow> (list_to_pair \<circ> f \<in> N \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<and> f \<in> space N \<rightarrow> space (listM M))"
proof-
  have A: "\<forall>x\<in>space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M). list_to_pair (pair_to_list x) = x"
    and B: "\<forall>y\<in>space (listM M). pair_to_list (list_to_pair y) = y"
    unfolding space_coprod_final_sink space_prod_initial_source
    using comp_list_to_list comp_pair_to_pair by auto
  show "\<And> f. (f \<in> (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o pair_to_list \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    and "\<And> f. (f o list_to_pair \<in> (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    and "\<And> f. (f \<in> N \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)) \<longleftrightarrow> (pair_to_list \<circ> f\<in> N \<rightarrow>\<^sub>M listM M \<and> f \<in> space N \<rightarrow> space (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M))"
    and "\<And> f. (f \<in> N \<rightarrow>\<^sub>M listM M) \<longleftrightarrow> (list_to_pair \<circ> f \<in> N \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<and> f \<in> space N \<rightarrow> space (listM M))"
    using measurable_isomorphism_iff[of pair_to_list"\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M" "(listM M)"list_to_pair _ N,OF pair_to_list_measurable list_to_pair_measurable A B] by blast+
qed

proposition measurable_iff_list_and_pair_plus:
  shows measurable_iff_pair_to_list_plus: "\<And> f. (f \<in> K \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda> q. ((fst q),pair_to_list (snd q))) \<in> K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    and measurable_iff_list_to_pair_plus: "\<And> f. (f \<in> K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda> p. ((fst p), list_to_pair (snd p))) \<in> K \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
proof-
  have 1: "(\<lambda> q. ((fst q),pair_to_list (snd q))) \<in> K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M K \<Otimes>\<^sub>M listM M"
    using pair_to_list_measurable by measurable
  have 2: "\<And>f. (\<lambda> p. ((fst p), list_to_pair (snd p))) \<in> K \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
    using list_to_pair_measurable by measurable
  have 3: "\<forall>x\<in>space (K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)).(fst (fst x, pair_to_list (snd x)), list_to_pair (snd (fst x, pair_to_list (snd x)))) = x"
    by(auto simp add: comp_pair_to_pair comp_def space_pair_measure space_prod_initial_source space_coprod_final_sink)
  have 4: "\<forall>y\<in>space (K \<Otimes>\<^sub>M listM M).(fst (fst y, list_to_pair (snd y)), pair_to_list (snd (fst y, list_to_pair (snd y)))) = y"
    by(auto simp add: comp_list_to_list comp_def space_pair_measure space_prod_initial_source space_coprod_final_sink)
  show "\<And>f. (f \<in> K \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<in> K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
    by(rule measurable_isomorphism_iff [OF 1 2 3 4])
  show "\<And> f. (f \<in> K \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda> p. ((fst p), list_to_pair (snd p))) \<in> K \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
    by(rule measurable_isomorphism_iff [OF 1 2 3 4])
qed

lemma measurable_iff_on_list:
  shows "\<And> f. (f \<in> (listM M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (\<forall> n\<in>UNIV. (f o pair_to_list o coProj n) \<in> (\<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M N)"
  by(auto simp add: measurable_iff_pair_to_list coprod_measurable_iff[THEN sym])


subsection\<open>measurability of functions defined inductively on lists\<close>

subsubsection \<open> Measurability of @{term Cons} \<close>

definition shift_prod :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "shift_prod x f = (\<lambda> m. if m = 0 then x else f(m - 1))"

lemma shift_prod_function:
  shows "(\<lambda> (x,xs).(shift_prod x xs)) \<in> space M \<times> (\<Pi>\<^sub>E i\<in>{..<n}. space M) \<rightarrow> (\<Pi>\<^sub>E i\<in>{..<(Suc n)}. space M)"
proof(clarify)
  fix x f assume x: "x \<in> (space M)" and f: "f \<in> {..<n} \<rightarrow>\<^sub>E space M"
  thus"shift_prod x f \<in> {..<Suc n} \<rightarrow>\<^sub>E space M"
    unfolding shift_prod_def
  proof(induction n)
    case 0
    thus ?case by(intro PiE_I, auto)
  next
    case (Suc n)
    assume f: "f \<in> {..<Suc n} \<rightarrow>\<^sub>E space M"
    show "(\<lambda>m. if m = 0 then x else f (m - 1)) \<in> {..<Suc (Suc n)} \<rightarrow>\<^sub>E space M"
    proof(intro PiE_I)
      fix m
      show "m \<in> {..<Suc (Suc n)} \<Longrightarrow> (if m = 0 then x else f (m - 1)) \<in> space M"
        using PiE_mem[OF f,where x ="m - 1"] x by auto
      show "m \<notin> {..<Suc (Suc n)} \<Longrightarrow> (if m = 0 then x else f (m - 1)) = undefined"
        using PiE_arb[OF f,where x ="m - 1"] x by auto
    qed
  qed
qed

lemma shift_prod_measurable:
  shows "(\<lambda> (x,xs).(shift_prod x xs)) \<in> M \<Otimes>\<^sub>M (prod_initial_source {..<n} (\<lambda>_.M)) \<rightarrow>\<^sub>M (prod_initial_source {..<(Suc n)} (\<lambda>_.M))"
  unfolding prod_initial_source_def
proof(rule measurable_initial_source2)
  show "(\<lambda>a. case a of (x, xs) \<Rightarrow> shift_prod x xs) \<in> space (M \<Otimes>\<^sub>M initial_source ({..<n} \<rightarrow>\<^sub>E space M) {(\<lambda>f. f i, M) |i. i \<in> {..<n}}) \<rightarrow> {..<Suc n} \<rightarrow>\<^sub>E space M"
    unfolding space_pair_measure by (metis shift_prod_function space_initial_source)
  show "\<forall>(f, Ma)\<in>{(\<lambda>f. f i, M) |i. i \<in> {..<Suc n}}. f \<in> ({..<Suc n} \<rightarrow>\<^sub>E space M) \<rightarrow> space Ma"
    by blast
  show "\<forall>(f, Ma)\<in>{(\<lambda>f. f i, M) |i. i \<in> {..<Suc n}}.
 (\<lambda>x. f (case x of (x, xs) \<Rightarrow> shift_prod x xs)) \<in> M \<Otimes>\<^sub>M initial_source ({..<n} \<rightarrow>\<^sub>E space M) {(\<lambda>f. f i, M) |i. i \<in> {..<n}} \<rightarrow>\<^sub>M Ma"
  proof(intro ballI, elim exE conjE CollectE)
    fix x :: "((nat \<Rightarrow> 'a) \<Rightarrow> 'a) \<times> 'a measure" and i assume x: "x = (\<lambda>f. f i, M)" and i: "i \<in> {..<Suc n}"
    show "case x of (f, N) \<Rightarrow> (\<lambda>x. f (case x of (x, xs) \<Rightarrow> shift_prod x xs)) \<in> M \<Otimes>\<^sub>M initial_source ({..<n} \<rightarrow>\<^sub>E space M) {(\<lambda>f. f i, M) |i. i \<in> {..<n}} \<rightarrow>\<^sub>M N"
    proof(cases"i = 0")
      case True
      hence *: "case x of (f, N) \<Rightarrow> (\<lambda>x. f (case x of (x, xs) \<Rightarrow> shift_prod x xs)) = fst"
        by (auto simp: case_prod_unfold shift_prod_def x i)
      thus ?thesis
        by (auto simp: x)
    next
      case False
      hence *: "(case x of (f, N) \<Rightarrow> (\<lambda>x. f (case x of (x, xs) \<Rightarrow> shift_prod x xs))) = (\<lambda> xa. xa(i - 1)) o snd"
        by (auto simp: case_prod_unfold comp_def shift_prod_def x i)
      have "(\<lambda> xa. xa(i - 1)) \<in> initial_source ({..<n} \<rightarrow>\<^sub>E space M) {(\<lambda>f. f i, M) |i. i \<in> {..<n}} \<rightarrow>\<^sub>M M"
      proof(intro measurable_initial_source1)
        show **: "((\<lambda> xa. xa(i - 1)),M) \<in> {(\<lambda>f. f i, M) |i. i \<in> {..<n}}"
          using False i by auto
        show "(\<lambda>xa. xa (i - 1)) \<in> ({..<n} \<rightarrow>\<^sub>E space M) \<rightarrow> space M"
          using i ** by fastforce
      qed
      thus ?thesis
        using * x by force
    qed
  qed
qed

lemma shift_prod_measurable':
  assumes "x \<in> (space M)"
  shows "(shift_prod x) \<in> (prod_initial_source {..<n} (\<lambda>_.M)) \<rightarrow>\<^sub>M (prod_initial_source {..<(Suc n)} (\<lambda>_.M))"
  using measurable_Pair2[OF shift_prod_measurable assms] by auto

definition shift_list :: "'a measure \<Rightarrow> 'a \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
  "shift_list M x =
    coTuple (UNIV :: nat set)
    (\<lambda> n :: nat. (space (prod_initial_source {..<n} (\<lambda>_.M))))
    (\<lambda> n :: nat. coProj (Suc n) o (shift_prod x))"

lemma shift_list_def2:
  shows "shift_list M x (n, f) = (Suc n, shift_prod x f)"
  unfolding shift_list_def shift_prod_def coTuple_def coProj_def by auto

lemma shift_list_measurable:
  shows "(\<lambda> (x,(n,f)). (shift_list M x (n,f))) \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
proof(subst measurable_iff_dist_law_A)
  show "countable (UNIV :: nat set)"
    by auto
  show "(\<lambda>(x, n, f). shift_list M x (n, f)) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S _\<in>{..<n}. M) M \<in> (\<amalg>\<^sub>M i\<in>UNIV. M \<Otimes>\<^sub>M (\<Pi>\<^sub>S _\<in>{..<i}. M)) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S _\<in>{..<n}. M)"
  proof(subst coprod_measurable_iff,intro ballI)
    fix i :: nat assume "i\<in>UNIV"
    thus "(\<lambda>(x, n, f). shift_list M x (n, f)) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S _\<in>{..<n}. M) M \<circ> coProj i \<in> M \<Otimes>\<^sub>M (\<Pi>\<^sub>S _\<in>{..<i}. M) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S _\<in>{..<n}. M)"
      using shift_prod_measurable[of M i ] coProj_measurable[of"Suc i"UNIV"(\<lambda> i. (\<Pi>\<^sub>S _\<in>{..<i}. M))"]
      by(subst measurable_cong, unfold coTuple_def shift_list_def dist_law_A_def shift_prod_def coProj_def, blast,auto)
  qed
qed

lemma shift_list_measurable':
  assumes "x \<in> (space M)"
  shows "(shift_list M x) \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
  using measurable_Pair2[OF shift_list_measurable[of M] assms] by auto

lemma measurable_Cons[measurable]:
  shows "(\<lambda> (x,xs). x # xs) \<in> M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M (listM M)"
proof-
  {
    fix x fix xs :: "_ list"
    have "x # xs = (pair_to_list o (\<lambda> (x,(n,f)). (shift_list M x (n,f)))) (x, list_to_pair xs)"
      unfolding shift_list_def coTuple_def  shift_prod_def
      by(induction xs ,auto simp add: comp_list_to_list coProj_def)
  }
  hence *: "(\<lambda> (x,xs). x # xs) = (pair_to_list o (\<lambda> (x,(n,f)). (shift_list M x (n,f)))) o (\<lambda> (x,xs :: _list). (x, list_to_pair xs))"
    by (auto simp: cond_case_prod_eta)
  show ?thesis
    using list_to_pair_measurable pair_to_list_measurable shift_list_measurable
    by(unfold *, measurable)
qed

lemma listM_Nil[measurable]:
  shows "Nil \<in> space (listM M)"
  unfolding listM_def space_initial_source by auto

lemma measurable_Cons'[measurable]:
  shows "x \<in> space M \<Longrightarrow> Cons x \<in> (listM M) \<rightarrow>\<^sub>M (listM M)"
  using measurable_Pair2 by auto

subsubsection \<open> Measurability of @{term"(\<lambda>p. [p])"}, the unit of list monad. \<close>

lemma measurable_unit_ListM[measurable]:
  shows "(\<lambda>p. [p]) \<in> M \<rightarrow>\<^sub>M listM M"
  by measurable

subsubsection \<open> Measurability of @{term rec_list} \<close>

text \<open>Since the notion of measurable functions does not support higher-order functions in general,
  the following theorems for measurability of@{term rec_list} are restricted. \<close>

lemma measurable_rec_list_func2':
  fixes T :: "'a \<Rightarrow> ('b \<Rightarrow> 'd)"
    and F :: "'a \<Rightarrow> 'c \<Rightarrow> 'c list \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'd)"
  assumes "(\<lambda>(a,b). T a b) \<in> K \<Otimes>\<^sub>M L \<rightarrow>\<^sub>M N "
    and "\<And>i g. (\<lambda> ((a, q), l). g a q l) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N
 \<Longrightarrow> (\<lambda>((a,b),x,l). (F a x ((pair_to_list o (coProj i)) l)) (\<lambda>q. (g a q l)) b) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    (*The condition is bit too strong*)
  shows "(\<lambda>((a,b),xs). (rec_list (T a) (F a)) xs b) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof(subst measurable_iff_pair_to_list_plus,subst measurable_iff_dist_laws)
  show "countable (UNIV :: nat set)"by auto
  show "(\<lambda>((a, b), xs). rec_list (T a) (F a) xs b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. M) (K \<Otimes>\<^sub>M L)
 \<in> (\<amalg>\<^sub>M i\<in>UNIV. (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)) \<rightarrow>\<^sub>M N"
    unfolding dist_law_A_def2
  proof(subst coprod_measurable_iff, intro ballI)
    fix i :: nat assume i: "i \<in> UNIV"
    show "(\<lambda>((a, b), xs). rec_list (T a) (F a) xs b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    proof(induction i)
      case 0
      have "((\<lambda>a. case a of (a, b) \<Rightarrow> (case a of (a, b) \<Rightarrow> \<lambda>xs. rec_list (T a) (F a) xs b) b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ>
 (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ>
 coProj 0) = ((\<lambda> (a,b). T a b) o fst)"
        by (auto simp: coProj_def )
      also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<0}. M) \<rightarrow>\<^sub>M N"
        using assms(1) by auto
      finally show ?case .
    next
      case (Suc i)
      have "((\<lambda>a. case a of (a, b) \<Rightarrow> (case a of (a, b) \<Rightarrow> \<lambda>xs. rec_list (T a) (F a) xs b) b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i)) = ((\<lambda>((a,b),x,l). (F a) x ((pair_to_list o (coProj i)) l) (rec_list (T a) (F a) ((pair_to_list o (coProj i)) l)) b) o (\<lambda> ((a,b),l). ((a,b),l 0,\<lambda>n. l(Suc n))))"
        using List.list.rec(2)
        by (auto simp: coProj_def)
      also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
      proof(rule measurable_comp)
        show "(\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n))) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
        proof(intro measurable_pair)
          have 1: "(\<lambda> l. l (0 :: nat)) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M"using
              measurable_prod_initial_source_projections by measurable
          have "fst \<circ> (snd \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) = (\<lambda> l. l 0) o snd"by auto
          also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M"
            using 1 by auto
          finally show "fst \<circ> (snd \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M".

          have "snd \<circ> (snd \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) = (\<lambda> l. \<lambda>n. l (Suc n)) o snd"by auto
          also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
            using measurable_projection_shift by measurable
          finally show "snd \<circ> (snd \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)".

          have "fst \<circ> (fst \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) = fst \<circ> fst"by auto
          also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M K"by auto
          finally show "fst \<circ> (fst \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M K".
          have "snd \<circ> (fst \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) = snd \<circ> fst"by auto
          also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M L"by auto
          finally show "snd \<circ> (fst \<circ> (\<lambda>((a, b), l). ((a, b), l 0, \<lambda>n. l (Suc n)))) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M L".
        qed

        show "(\<lambda>((a, b), x, l). F a x ((pair_to_list \<circ> coProj i) l) (rec_list (T a) (F a) ((pair_to_list \<circ> coProj i) l)) b)
 \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
        proof(intro assms(2)[of"\<lambda> a b l. (rec_list (T a) (F a) ((pair_to_list \<circ> coProj i) l)) b"i])
          have "(\<lambda>((a, q), l). rec_list (T a) (F a) ((pair_to_list \<circ> coProj i) l) q) = (\<lambda>a. case a of (a, b) \<Rightarrow> (case a of (a, b) \<Rightarrow> \<lambda>xs. rec_list (T a) (F a) xs b) b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ>
(\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ>
coProj i"
            by (auto simp: coProj_def)
          also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"using Suc by measurable
          finally show "(\<lambda>((a, q), l). rec_list (T a) (F a) ((pair_to_list \<circ> coProj i) l) q) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N".
        qed
      qed
      finally show ?case .
    qed
  qed
qed

lemma measurable_rec_list_func2:
  fixes T :: "'a \<Rightarrow> ('b \<Rightarrow> 'd)"
    and F :: "'a \<Rightarrow> 'c \<Rightarrow> 'c list \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'd)"
  assumes "(\<lambda>(a,b). T a b) \<in> K \<Otimes>\<^sub>M L \<rightarrow>\<^sub>M N "
    and "\<And>i g. (\<lambda> (a, q, l). g a q l) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N
 \<Longrightarrow> (\<lambda>(a,b,x,l). (F a x ((pair_to_list o (coProj i)) l)) (\<lambda>q. (g a q l)) b) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    (*The condition is bit too strong*)
  shows "(\<lambda>(a,b,xs). (rec_list (T a) (F a)) xs b) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof-
  {
    fix i :: nat and g
    assume g: "(\<lambda> ((a, q), l). g a q l) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    have "(\<lambda> (a, q, l). g a q l) = (\<lambda> ((a, q), l). g a q l) o (\<lambda> (a, q, l). ((a, q), l))"
      by auto
    also have "... \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
      using g by measurable
    finally have g2: "(\<lambda>(a, q, l). g a q l) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N".

    hence m: "(\<lambda>(a,b,x,l). (F a x ((pair_to_list o (coProj i)) l)) (\<lambda>q. (g a q l)) b) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
      using assms(2) by measurable
    have "(\<lambda>((a,b),x,l). (F a x ((pair_to_list o (coProj i)) l)) (\<lambda>q. (g a q l)) b) = ((\<lambda>(a,b,x,l). (F a x ((pair_to_list o (coProj i)) l)) (\<lambda>q. (g a q l)) b)) o (\<lambda>((a,b),x,l).(a,b,x,l))"by auto
    also have "... \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
      using m by measurable
    finally have F: "(\<lambda>((a, b), x, l). F a x ((pair_to_list \<circ> coProj i) l) (\<lambda>q. g a q l) b) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N".
  }
  note 2 = this
  have 3: "(\<lambda>((a,b),xs). (rec_list (T a) (F a)) xs b) \<in> (K \<Otimes>\<^sub>M L) \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
    by(rule measurable_rec_list_func2'[OF assms(1) 2],auto)
  have "(\<lambda>(a,b,xs). (rec_list (T a) (F a)) xs b) = (\<lambda>((a,b),xs). (rec_list (T a) (F a)) xs b) o (\<lambda>(a,b,xs).((a,b),xs))"
    by auto
  also have "... \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"using 3 by measurable
  finally show "(\<lambda>(a, b, xs). rec_list (T a) (F a) xs b) \<in> K \<Otimes>\<^sub>M L \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N".
qed

lemma measurable_rec_list'_func:
  fixes T :: "('c \<Rightarrow> 'd)"
    and F :: "'b \<Rightarrow> 'b list \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd)"
  assumes "T \<in> K \<rightarrow>\<^sub>M N "
    and "\<And>i g. g \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N
 \<Longrightarrow> (\<lambda>p. (F (fst (snd p)) (pair_to_list (coProj i(snd (snd (p))))) (\<lambda>q. (g (q,snd (snd (p)))))) (fst p)) \<in> K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    (*The condition is bit too strong*)
  shows "(\<lambda>p. (rec_list T F) (snd p) (fst p)) \<in> K \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof(subst measurable_iff_pair_to_list_plus,subst measurable_iff_dist_laws)
  show "countable (UNIV :: nat set)"by auto
  show "(\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. M) K \<in> (\<amalg>\<^sub>M i\<in>UNIV. K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)) \<rightarrow>\<^sub>M N"
    unfolding dist_law_A_def2
  proof(subst coprod_measurable_iff, intro ballI)
    fix i :: nat assume "i \<in> UNIV"
    show "(\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    proof(induction i)
      case 0
      {
        fix p :: "(_ \<times> (nat\<Rightarrow>_))" assume "p \<in> space (K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<0}. M))"

        hence "(snd p) = (\<lambda> n. undefined)"
          unfolding space_pair_measure space_prod_initial_source by auto
        hence "((\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj 0) p = T (fst p)"
          by (auto simp: case_prod_beta comp_def coProj_def)
      }note * = this
      thus ?case
        by(subst measurable_cong[OF *],auto intro: assms measurable_compose)
    next
      case (Suc i)
      have eq1: "(\<lambda>p. (rec_list T F (pair_to_list (i,(snd p)))) (fst p)) = (\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i"
        by (auto simp: coProj_def comp_def)
      also have "... \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"using local.Suc by blast
      finally have meas1: "(\<lambda>p. (rec_list T F (pair_to_list (i,(snd p)))) (fst p)) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N".
      {
        fix p :: "(_ \<times> (nat\<Rightarrow>_))" assume "p \<in> space (K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M))"
        hence "(pair_to_list (Suc i,snd p)) = ((snd p 0) # (pair_to_list (i,\<lambda>n. (snd p)(Suc n))))"
          by auto
        hence "((\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i)) p =
 rec_list T F ((snd p 0) # (pair_to_list (i,\<lambda>n. (snd p)(Suc n))))(fst p)
 "
          by (auto simp: coProj_def)
        also have "... = F (snd p 0) (pair_to_list (i,\<lambda>n. (snd p)(Suc n))) (rec_list T F (pair_to_list (i,\<lambda>n. (snd p)(Suc n)))) (fst p)"
          by auto
        finally have "((\<lambda>p. rec_list T F (snd p) (fst p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i)) p = ((\<lambda>p. F (fst (snd p)) (pair_to_list (coProj i (snd (snd p)))) (\<lambda>q. rec_list T F (pair_to_list (i, snd (q, snd (snd p)))) (fst (q, snd (snd p)))) (fst p)) o (\<lambda> p. (fst p,snd p 0, \<lambda>n. (snd p)(Suc n)))) p"
          by (auto simp: coProj_def)
      }note * = this
      show ?case
      proof(subst measurable_cong[OF *])
        show "\<And> w. w \<in> space (K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)) \<Longrightarrow> w \<in> space (K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M))"by auto
        show "(\<lambda>p. F (fst (snd p)) (pair_to_list (coProj i (snd (snd p)))) (\<lambda>q. rec_list T F (pair_to_list (i, snd (q, snd (snd p)))) (fst (q, snd (snd p)))) (fst p)) \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n)))
 \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
        proof(rule measurable_comp)
          show "(\<lambda>p. F (fst (snd p)) (pair_to_list (coProj i (snd (snd p)))) (\<lambda>q. rec_list T F (pair_to_list (i, snd (q, snd (snd p)))) (fst (q, snd (snd p)))) (fst p)) \<in> K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
            using assms(2)[OF meas1] by auto
          show "(\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n))) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) "
          proof(intro measurable_pair)
            have eq1: "fst \<circ> (snd \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n)))) = (\<lambda>p. p 0) o snd"by auto
            have eq2: "snd \<circ> (snd \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n)))) = (\<lambda>p. \<lambda>n. p (Suc n)) o snd"by auto
            show "fst \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n))) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M K"by(auto simp: comp_def)
            show "fst \<circ> (snd \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n)))) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M"
              by(subst eq1, auto intro: measurable_comp measurable_prod_initial_source_projections)
            show "snd \<circ> (snd \<circ> (\<lambda>p. (fst p, snd p 0, \<lambda>n. snd p (Suc n)))) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
            proof(subst eq2,rule measurable_comp)
              show "snd \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"by auto
              show "(\<lambda>p n. p (Suc n)) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
                by(rule measurable_prod_initial_sourceI,unfold space_prod_initial_source, auto intro :measurable_prod_initial_source_projections)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma measurable_rec_list''_func:
  fixes T :: "('c \<Rightarrow> 'd)"
    and F :: "'b \<Rightarrow> 'b list \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd)"
  assumes "T \<in> K \<rightarrow>\<^sub>M N"
    and "\<And>i g. (\<lambda>(q,v). g q v) \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N
 \<Longrightarrow> (\<lambda>(x,y,xs). (F y (pair_to_list (coProj i xs)) (\<lambda>q. (g q xs))) x) \<in> K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
  shows "(\<lambda>(x,xs). (rec_list T F) xs x) \<in> K \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof-
  {
    fix i :: nat and g assume "g \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    hence "(\<lambda>x. F (fst (snd x)) (pair_to_list (coProj i (snd (snd x)))) (\<lambda>q. g (q, snd (snd x))) (fst x)) \<in> K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
      using assms(2)[of"(\<lambda>q xs. g (q, xs))"] by (auto simp: case_prod_beta')
  }
  hence "\<And>i g. g \<in> K \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N \<Longrightarrow> (\<lambda>x. F (fst (snd x)) (pair_to_list (coProj i (snd (snd x)))) (\<lambda>q. g (q, snd (snd x))) (fst x)) \<in> K \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"by auto
  thus ?thesis using assms(1) measurable_rec_list'_func by measurable
qed

lemma measurable_rec_list':
  assumes "F \<in> (N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
  shows "(\<lambda>p. (rec_list (fst p) (\<lambda> y xs x. F(x,y,xs)) (snd p))) \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof(subst measurable_iff_list_and_pair_plus, subst measurable_iff_dist_laws measurable_iff_dist_laws)
  show "countable (UNIV :: nat set)"by auto
  show "(\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. M) N \<in> (\<amalg>\<^sub>M i\<in>UNIV. N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)) \<rightarrow>\<^sub>M N"
    unfolding dist_law_A_def2
  proof(subst coprod_measurable_iff, intro ballI)
    fix i :: nat assume "i \<in> UNIV"
    show "(\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    proof(induction i)
      case 0
      {
        fix p :: "(_ \<times> (nat\<Rightarrow>_))" assume "p \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<0}. M))"
        hence "(snd p) = (\<lambda> n. undefined)"
          unfolding space_pair_measure space_prod_initial_source by auto
        hence "((\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj 0) p = fst p"
          by (auto simp: case_prod_beta comp_def coProj_def)
      }note * = this
      show ?case
        by(subst measurable_cong[OF *],auto)
    next
      case (Suc i)
      define X where "X = (\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i"
      hence X[measurable]: "X \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
        by (auto simp: local.Suc)
      {
        fix p :: "(_ \<times> (nat\<Rightarrow>_))" assume "p \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M))"
        hence
          "((\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i)) p
 = rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (pair_to_list (Suc i, snd p))"
          by (auto simp: case_prod_beta comp_def coProj_def)
        also have "... =F(((\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj i)(fst p , \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n)))"
          by(auto simp: case_prod_beta comp_def coProj_def)
        also have "... = (F o (\<lambda> p. (X (fst p , \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) p"
          unfolding X_def by auto
        finally have "((\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i)) p = (F o (\<lambda> p. (X (fst p , \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) p".
      }note * = this

      show "(\<lambda>p. rec_list (fst p) (\<lambda>y xs x. F (x, y, xs)) (snd p)) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> (\<lambda>p. (fst (snd p), fst p, snd (snd p))) \<circ> coProj (Suc i) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
      proof(subst measurable_cong[OF *])
        show "\<And>w. w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)) \<Longrightarrow> w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M))"by auto
        show "F \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
        proof(intro measurable_comp)
          show "F \<in> (N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"by (auto simp: assms(1))
          show "(\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M listM M"
          proof(intro measurable_pair)
            have "fst \<circ> (snd \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) = (\<lambda>p. p 0) o snd"by auto
            also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M"
            proof(rule measurable_comp)
              show "snd \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"by auto
              show "(\<lambda>p. p 0) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M"
                unfolding prod_initial_source_def by(rule measurable_initial_source1,auto)
            qed
            finally show "fst \<circ> (snd \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M M".

            have "snd \<circ> (snd \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) = (\<lambda>p. pair_to_list (i, \<lambda>n. p (Suc n))) o snd"by auto
            also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M listM M"
            proof(rule measurable_comp)
              show "snd \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"by auto
              have "(\<lambda>p. pair_to_list (i, \<lambda>n. p (Suc n))) = pair_to_list o (coProj i) o (\<lambda>p. (\<lambda>n. p (Suc n)))"
                by(auto simp: comp_def coProj_def)
              also have "... \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M listM M"
              proof(subst measurable_iff_prod_initial_source,intro measurable_comp)
                show "(\<lambda>p n. if n = 0 then fst p else snd p (n - 1)) \<in> M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"
                  by(auto simp: measurable_integrate_prod_initial_source_Suc_n)
                show "pair_to_list \<in> (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M (listM M)"
                  by(auto simp: pair_to_list_measurable)
                show "coProj i \<in>(\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M n\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<n}. M)"
                  by auto
                show "(\<lambda>p n. p (Suc n)) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
                  by(auto simp: measurable_projection_shift)
              qed
              finally show "(\<lambda>p. pair_to_list (i, \<lambda>n. p (Suc n))) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M listM M".
            qed
            finally show "snd \<circ> (snd \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n))))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M listM M".
            have "fst \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n)))) = X o (\<lambda>p. (fst p, \<lambda>n. snd p (Suc n)))"by auto
            also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
            proof(rule measurable_comp)
              show "X \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"by(auto simp: X)
              show "(\<lambda>p. (fst p, \<lambda>n. snd p (Suc n))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
              proof(rule measurable_pair)
                show "fst \<circ> (\<lambda>p. (fst p, \<lambda>n. snd p (Suc n))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
                  by (auto simp: measurable_cong_simp)
                have "snd \<circ> (\<lambda>p. (fst p, \<lambda>n. snd p (Suc n))) = (\<lambda>p n. p (Suc n)) o snd"by auto
                also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
                proof(rule measurable_comp)
                  show "snd \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"by auto
                  show "(\<lambda>p n. p (Suc n)) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)"
                    by(auto simp: measurable_projection_shift)
                qed
                finally show "snd \<circ> (\<lambda>p. (fst p, \<lambda>n. snd p (Suc n))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. M)".
              qed
            qed
            finally show "fst \<circ> (\<lambda>p. (X (fst p, \<lambda>n. snd p (Suc n)), snd p 0, pair_to_list (i, \<lambda>n. snd p (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N".
          qed
        qed
      qed
    qed
  qed
qed

lemma measurable_rec_list'2:
  assumes "(\<lambda>p. (F (fst (snd p)) (snd (snd p)) (fst p))) \<in> (N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
  shows "(\<lambda>p. (rec_list (fst p) F (snd p))) \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
  using measurable_rec_list'[OF assms] by auto

lemma measurable_rec_list:
  assumes "F \<in> (N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
    and "T \<in> space N"
  shows "rec_list T (\<lambda> y xs x. F(x,y,xs)) \<in> (listM M) \<rightarrow>\<^sub>M N"
proof-
  have "rec_list T (\<lambda> y xs x. F(x,y,xs)) = (\<lambda>p. (rec_list (fst p) (\<lambda> y xs x. F(x,y,xs)) (snd p))) o (\<lambda> r.(T, r))"
    by auto
  also have "... \<in> (listM M) \<rightarrow>\<^sub>M N"
    using measurable_rec_list' assms by measurable
  finally show ?thesis .
qed

lemma measurable_rec_list2:
  assumes "(\<lambda>p. (F (fst (snd p)) (snd (snd p)) (fst p))) \<in> (N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N)"
    and "T \<in> space N"
  shows "rec_list T F \<in> (listM M) \<rightarrow>\<^sub>M N"
  using measurable_rec_list[OF assms] by auto

lemma measurable_rec_list''':
  assumes "(\<lambda>(x,y,xs). F x y xs) \<in> N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
    and "T \<in> space N"
  shows "rec_list T (\<lambda> y xs x. F x y xs) \<in> (listM M) \<rightarrow>\<^sub>M N"
  using measurable_rec_list[OF assms] by fastforce

subsubsection \<open> Measurability of @{term case_list} \<close>

lemma measurable_case_list[measurable(raw)]:
  assumes [measurable]:"(\<lambda>p. (F (fst p) (snd p))) \<in> M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N "
    and "T \<in> space N"
  shows "case_list T F \<in> (listM M) \<rightarrow>\<^sub>M N"
proof(subst measurable_iff_list_and_pair, subst coprod_measurable_iff, rule ballI)
  note [measurable] = measurable_decompose_prod_initial_source_Suc_n
  fix i :: nat assume i: "i \<in> UNIV"
  show "case_list T F \<circ> pair_to_list \<circ> coProj i \<in> (\<Pi>\<^sub>S i\<in>{..<i}. M) \<rightarrow>\<^sub>M N"
    unfolding comp_def coProj_def
  proof(induction i)
    case 0
    thus "(\<lambda>x. case pair_to_list (0, x) of [] \<Rightarrow> T | z # zs \<Rightarrow> F z zs) \<in> (\<Pi>\<^sub>S i\<in>{..<0}. M) \<rightarrow>\<^sub>M N"
      using assms(2) by auto
  next
    case (Suc i)
    {
      fix y assume "y \<in> space (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"
      then obtain z zs where pair: "pair_to_list (Suc i, y) = z # zs" and z : "z = y 0" and zs: "zs = pair_to_list(i, (\<lambda>n :: nat. y(Suc n)))"
        by auto
      hence "(\<lambda>x. case pair_to_list (Suc i, x) of [] \<Rightarrow> T | z # zs \<Rightarrow> F z zs) y = F z zs"
        by auto
      also have "... = ((\<lambda>p. (F (fst p) (snd p))) o (\<lambda> p. ((fst p),(pair_to_list o (coProj i))(snd p))) o (\<lambda> f. (f 0, (\<lambda> n. f (Suc n))))) y"
        by (auto simp: z zs coProj_def)
      finally have "(case pair_to_list (Suc i, y) of [] \<Rightarrow> T | z # zs \<Rightarrow> F z zs) = ((\<lambda>p. F (fst p) (snd p)) \<circ> (\<lambda>p. (fst p, (pair_to_list \<circ> coProj i) (snd p))) \<circ> (\<lambda>f. (f 0, \<lambda>n. f (Suc n)))) y".
    }note * = this
    show ?case
      unfolding coProj_def
    proof(subst measurable_cong[OF *])
      show "\<And>w. w \<in> space (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<Longrightarrow> w \<in> space (\<Pi>\<^sub>S i\<in>{..<Suc i}. M)"
        by auto
      show "(\<lambda>p. F (fst p) (snd p)) \<circ> (\<lambda>p. (fst p, (pair_to_list \<circ> coProj i) (snd p))) \<circ> (\<lambda>f. (f 0, \<lambda>n. f (Suc n))) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc i}. M) \<rightarrow>\<^sub>M N"
        unfolding comp_def using pair_to_list_measurable assms by measurable
    qed
  qed
qed

lemma measurable_case_list2[measurable]:
  assumes [measurable]:"(\<lambda>(x,b,bl). g x b bl) \<in> N \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (listM L) \<rightarrow>\<^sub>M M"
    and [measurable]:"a \<in> N \<rightarrow>\<^sub>M M"
  shows "(\<lambda>(x,xs). case_list (a x) (g x) xs) \<in> N \<Otimes>\<^sub>M (listM L) \<rightarrow>\<^sub>M M"
proof(subst measurable_iff_list_and_pair_plus, subst measurable_iff_dist_laws)
  note [measurable] = pair_to_list_measurable list_to_pair_measurable dist_law_A_measurable measurable_projection_shift
  show "countable (UNIV :: nat set)"
    by auto
  show "(\<lambda>(x, y). case_list (a x) (g x) y) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. L) N \<in> (\<amalg>\<^sub>M i\<in>UNIV. N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. L)) \<rightarrow>\<^sub>M M"
  proof(subst coprod_measurable_iff,rule ballI)
    fix i :: nat assume i: "i \<in> (UNIV :: nat set)"
    show "(\<lambda>(x, y). case_list (a x) (g x) y) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. L) N \<circ> coProj i \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<i}. L) \<rightarrow>\<^sub>M M"
    proof(induction i)
      case 0
      {
        fix w :: "'a \<times> (nat \<Rightarrow> 'b)" assume "w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<0}. L))"
        have "((\<lambda>b. case b of (x, []) \<Rightarrow> a x | (x, a # b) \<Rightarrow> g x a b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. L) N \<circ> coProj 0) w = (a (fst w))"
          unfolding comp_def coProj_def dist_law_A_def2 pair_to_list.simps by auto
      }note * = this
      show ?case
        using assms by(subst measurable_cong[OF *],measurable)
    next
      case (Suc i)
      {
        fix w :: "'a \<times> (nat \<Rightarrow> 'b)" assume "w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L))"
        have "((\<lambda>b. case b of (x, []) \<Rightarrow> a x | (x, a # b) \<Rightarrow> g x a b) \<circ> (\<lambda>q. (fst q, pair_to_list (snd q))) \<circ> dist_law_A UNIV (\<lambda>n. \<Pi>\<^sub>S i\<in>{..<n}. L) N \<circ> coProj (Suc i)) w = ((\<lambda>(x,b,bl). g x b bl) \<circ> (\<lambda> w. (fst w, (((snd w) 0) , (pair_to_list (i, \<lambda> n. (snd w)(Suc n))))))) w "
          unfolding comp_def coProj_def dist_law_A_def2 pair_to_list.simps by auto
      }note * = this
      show ?case
      proof(subst measurable_cong[OF *])
        show "\<And>w. w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L)) \<Longrightarrow> w \<in> space (N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L))"
          by auto
        show "(\<lambda>(x, xa, y). g x xa y) \<circ> (\<lambda>w. (fst w, snd w 0, pair_to_list (i, \<lambda>n. snd w (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M M"
        proof(rule measurable_comp)
          show "(\<lambda>w. (fst w, snd w 0, pair_to_list (i, \<lambda>n. snd w (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M N \<Otimes>\<^sub>M (L \<Otimes>\<^sub>M (listM L))"
          proof(intro measurable_pair)
            show "fst \<circ> (\<lambda>w. (fst w, snd w 0, pair_to_list (i, \<lambda>n. snd w (Suc n)))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M N"
              by(auto simp: comp_def)
            have "(\<lambda>x. snd x 0) = ((\<lambda>f. f 0) o snd)"
              by auto
            also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M L"
              by(auto intro: measurable_comp measurable_prod_initial_source_projections)
            finally have "(\<lambda>x. snd x 0) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M L".
            thus"fst \<circ> (snd \<circ> (\<lambda>w. (fst w, snd w 0, pair_to_list (i, \<lambda>n. snd w (Suc n))))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M L"
              unfolding comp_def prod_initial_source_def using pair_to_list_measurable[of L] by auto
            have "(\<lambda>x. pair_to_list (i, \<lambda>n. snd x (Suc n))) = pair_to_list o (coProj i) o (\<lambda> f. \<lambda>n. f (Suc n)) o snd"
              by(auto simp: comp_def coProj_def)
            also have "... \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M (listM L)"
            proof(intro measurable_comp)
              show "coProj i \<in> (\<Pi>\<^sub>S i\<in>{..<i}. L) \<rightarrow>\<^sub>M ((\<amalg>\<^sub>M i\<in>UNIV. \<Pi>\<^sub>S i\<in>{..<i}. L))"
                by auto
            qed(auto)
            finally have "(\<lambda>x. pair_to_list (i, \<lambda>n. snd x (Suc n))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M listM L".
            thus"snd \<circ> (snd \<circ> (\<lambda>w. (fst w, snd w 0, pair_to_list (i, \<lambda>n. snd w (Suc n))))) \<in> N \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc i}. L) \<rightarrow>\<^sub>M listM L"
              unfolding comp_def by auto
          qed
          show "(\<lambda>(x, xa, y). g x xa y) \<in> N \<Otimes>\<^sub>M L \<Otimes>\<^sub>M listM L \<rightarrow>\<^sub>M M"
            by (auto simp: assms)
        qed
      qed
    qed
  qed
qed

lemma measurable_case_list':
  assumes "(\<lambda>(x,b,bl). g x b bl) \<in> N \<Otimes>\<^sub>M L \<Otimes>\<^sub>M (listM L) \<rightarrow>\<^sub>M M"
    and "a \<in> N \<rightarrow>\<^sub>M M"
    and "l \<in> N \<rightarrow>\<^sub>M listM L"
  shows "(\<lambda>x. case_list (a x) (g x) (l x)) \<in> N \<rightarrow>\<^sub>M M"
  using measurable_case_list2 assms by measurable

subsubsection \<open> Measurability of @{term foldr} \<close>

lemma measurable_foldr:
  assumes "(\<lambda> (x,y). F x y) \<in> (N \<Otimes>\<^sub>M M \<rightarrow>\<^sub>M N)"
  shows "(\<lambda> (T,xs). foldr (\<lambda> x y. F y x) xs T) \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof-
  have 1: "(\<lambda> (x ,y , xs). (\<lambda> y xs x. F x y) y xs x) \<in> N \<Otimes>\<^sub>M M \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N"
    using assms by measurable
  {
    fix T xs
    have "(foldr (\<lambda> x y. F y x) xs T) = (rec_list T (\<lambda> y xs x. F x y) xs)"
      by(induction xs,auto)
  }
  hence "(\<lambda> (T,xs). foldr (\<lambda> x y. F y x) xs T) = (\<lambda> (T,xs). (rec_list T (\<lambda> y xs x. (\<lambda> (x ,y , xs). (\<lambda> y xs x. F x y) y xs x)(x,y,xs)) xs))"
    by auto
  also have "... \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
    using measurable_rec_list'[OF 1 ] by measurable
  finally show ?thesis .
qed

subsubsection \<open> Measurability of @{term append} \<close>

lemma measurable_append[measurable]:
  shows "(\<lambda> (xs,ys). xs @ ys) \<in> (listM M) \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M (listM M)"
proof-
  {
    fix xs ys :: "'a list"
    have "xs @ ys = (rec_list ys (\<lambda>x xs ys. x # ys)) xs"
      by(induction xs,auto)
  }
  hence "(\<lambda> (xs :: 'a list,ys :: 'a list). xs @ ys) = (\<lambda>p. rec_list (fst p) (\<lambda>x xs ys. x # ys) (snd p)) o (\<lambda>(xs, ys). (ys, xs))"
    by auto
  also have "... \<in> (listM M) \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M (listM M)"
    using measurable_rec_list'2 by measurable
  finally show ?thesis .
qed

subsubsection \<open> Measurability of @{term rev} \<close>

lemma measurable_rev[measurable]:
  shows "rev \<in> (listM M) \<rightarrow>\<^sub>M (listM M)"
proof-
  note [measurable] = measurable_pair listM_Nil
  have "rev = (\<lambda> xs :: 'a list. rec_list [] (\<lambda>y xs x. (((\<lambda>(xs, ys). xs @ ys)o (\<lambda>p. (fst p,[fst (snd p)]))) (x, y, xs))) xs)"
    by (auto simp add: rev_def)
  also have "... \<in> listM M \<rightarrow>\<^sub>M listM M"
    by(rule measurable_rec_list,measurable)
  finally show ?thesis .
qed

subsubsection \<open> Measurability of @{term concat}, that is, the bind of the list monad\<close>

lemma measurable_concat[measurable]:
  shows "concat \<in> listM (listM M) \<rightarrow>\<^sub>M (listM M)"
proof-
  note [measurable] = measurable_append listM_Nil
  have "concat = (\<lambda> xs :: 'a list list. rec_list [] (\<lambda>y xs x. (((\<lambda>(xs, ys). xs @ ys) o (\<lambda>p. (fst (snd p), fst p))) (x, y, xs))) xs)"
    by (auto simp add: concat_def comp_def)
  also have "... \<in> listM (listM M) \<rightarrow>\<^sub>M listM M"
    by(rule measurable_rec_list,measurable)
  finally show ?thesis .
qed

subsubsection \<open> Measurability of @{term map}, the functor part of the list monad\<close>

lemma measurable_map[measurable]:
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M N "
  shows "(map f) \<in> (listM M) \<rightarrow>\<^sub>M (listM N)"
proof-
  note [measurable] = measurable_pair listM_Nil
  {
    fix xs  :: "'a list"
    have "map f xs = (rec_list [] (\<lambda>x xs ys. (f x) # ys)) xs"
      by(induction xs,auto)
  }
  hence "(map f) = (\<lambda>p. (rec_list [] (\<lambda>y' xs' x'. ((\<lambda> (x,xs). x # xs) o (\<lambda>p. (f (fst (snd p)), fst p))) (x', y', xs')) p))"
    by auto
  also have "... \<in> listM M \<rightarrow>\<^sub>M listM N"
    by(rule measurable_rec_list, measurable)
  finally show ?thesis.
qed

subsubsection \<open> Measurability of @{term length} \<close>

lemma measurable_length[measurable]:
  shows "length \<in> listM M \<rightarrow>\<^sub>M count_space (UNIV :: nat set)"
proof -
  {
    fix xs :: "'a list"
    have "length xs = (rec_list 0 (\<lambda>y xs x. (Suc o fst) (x, y ,xs))) xs "
      by(induction xs,auto)
  }
  hence "length = (\<lambda> xs :: 'a list.(rec_list 0 (\<lambda>y xs x :: nat. (Suc o fst) (x, y ,xs)) xs))"
    by auto
  also have "... \<in> listM M \<rightarrow>\<^sub>M count_space UNIV"
    by(rule measurable_rec_list, auto)
  finally show ?thesis .
qed

lemma sets_listM_length[measurable]:
  shows "{xs. xs \<in> space (listM M) \<and> length xs = n} \<in> sets (listM M)"
  by measurable

subsubsection \<open> Measurability of @{term foldl} \<close>

lemma measurable_foldl [measurable]:
  assumes [measurable]:"(\<lambda>(x,y). F y x) \<in> (M \<Otimes>\<^sub>M N \<rightarrow>\<^sub>M N)"
  shows "(\<lambda> (T,xs). foldl F T xs) \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof(subst foldl_conv_foldr)
  have "(\<lambda>(T, xs). foldr (\<lambda>x y. F y x) (rev xs) T) = (\<lambda>(T, xs). foldr (\<lambda>x y. F y x) xs T) o (\<lambda>(T, xs). (T, rev xs))"
    by auto
  also have "... \<in> N \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N"
    using measurable_foldr by measurable
  finally show "(\<lambda>(T, xs). foldr (\<lambda>x y. F y x) (rev xs) T) \<in> N \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N".
qed

subsubsection \<open> Measurability of @{term fold} \<close>

lemma measurable_fold [measurable]:
  assumes [measurable]: "(\<lambda>(x,y). F x y) \<in> (M \<Otimes>\<^sub>M N\<rightarrow>\<^sub>M N)"
  shows "(\<lambda> (T,xs). fold F xs T) \<in> N \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M N"
proof-
  have "(\<lambda> (T,xs). fold F xs T) = (\<lambda> (T,xs). foldr F xs T) o (\<lambda> (T,xs). (T, rev xs))"
    by (auto simp add: foldr_conv_fold)
  also have "... \<in> N \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N"
    using measurable_foldr by measurable
  finally show "(\<lambda>(T, xs). fold F xs T) \<in> N \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M N".
qed

subsubsection \<open> Measurability of @{term drop} \<close>

lemma measurable_drop[measurable]:
  shows "drop n \<in> listM M \<rightarrow>\<^sub>M listM M"
proof-
  have "(\<lambda>a. []) \<in> space (Pi\<^sub>M UNIV (\<lambda>a. listM M))"
    using listM_Nil space_PiM by fastforce
  with measurable_rec_list''' listM_Nil space_PiM
  show ?thesis unfolding drop_def by measurable
qed

lemma measurable_drop'[measurable]:
  shows "(\<lambda> (n,xs). drop n xs) \<in> count_space (UNIV :: nat set) \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M listM M"
  by measurable

subsubsection \<open> Measurability of @{term take} \<close>

lemma measurable_take[measurable]:
  shows "take n \<in> listM M \<rightarrow>\<^sub>M listM M"
proof-
  have "(\<lambda> (n,xs). take n xs) = (\<lambda> (n,xs). rev (drop (length xs - n) (rev xs)))"
    by (metis rev_swap rev_take)
  also have "... \<in> count_space (UNIV :: nat set) \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M listM M"
    using measurable_drop by measurable
  finally show ?thesis by measurable
qed

lemma measurable_take'[measurable]:
  shows "(\<lambda> (n,xs). take n xs) \<in> count_space (UNIV :: nat set) \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M listM M"
  by measurable

subsubsection \<open> Measurability of @{term nth} plus a default value \<close>

text \<open> Since the {@term undefined} is harmful to prove measurability, we introduce the total function version of @{term nth} that returns a fixed default value when the nth element is not found. \<close>

primrec nth_total  :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "nth_total d [] n = d" |
  "nth_total d (x # xs) n = (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> nth_total d xs k)"

value"nth_total (15 :: nat) [] (0 :: nat)  :: nat"
value"nth_total (15 :: nat) [1] (0 :: nat)  :: nat"
value"nth_total (15 :: nat) [1,2,3] (0 :: nat)  :: nat"
value"nth_total (15 :: nat) [1,2,3] (1 :: nat)  :: nat"
value"nth_total (15 :: nat) [1,2,3] (2 :: nat)  :: nat"
value"nth_total (15 :: nat) [1,2,3] (3 :: nat)  :: nat"
  (* value"nth [] (0 :: nat)  :: nat" *)
value"nth [1] (0 :: nat)  :: nat"
value"nth [1,2,3] (0 :: nat)  :: nat"
value"nth [1,2,3] (1 :: nat)  :: nat"
value"nth [1,2,3] (2 :: nat)  :: nat"
  (* value"nth [1,2,3] (3 :: nat)  :: nat"*)

text \<open> The total version @{term nth_total} is the same as @{term nth} if the nth element exists and otherwise it returns the default value.  \<close>

lemma cong_nth_total_nth:
  shows "((n :: nat) < length xs \<and> 0 < length xs) \<Longrightarrow> nth_total d xs n = nth xs n"
proof(induction xs arbitrary :n)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  show "nth_total d (a # xs) n = (a # xs) ! n"
  proof(cases"n=0")
    case True
    thus ?thesis by auto
  next
    case False
    hence 1: "n = Suc (n-1)" and 3: "n-1 < length xs"
      using Cons(2) by auto
    hence 2: "nth_total d xs (n-1) = xs ! (n-1)"
      using Cons(1) by fastforce
    thus ?thesis unfolding nth_total.simps(2) nth.simps
      by (metis"2"Nitpick.case_nat_unfold)
  qed
qed

lemma cong_nth_total_default:
  shows "\<not>((n :: nat) < length xs \<and> 0 < length xs) \<Longrightarrow> nth_total d xs n = d"
proof(induction xs arbitrary :n)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  hence "0 < length (a # xs)" by auto
  then obtain m where n: "n = Suc m"
    using Cons.prems not0_implies_Suc by force
  thus ?case unfolding n nth_total.simps using Cons.IH[of m]
    using Cons.prems n by auto
qed

lemma nth_total_def2:
  shows " nth_total d xs n = (if (n < length xs \<and> 0 < length xs) then xs ! n else d)"
  using cong_nth_total_nth cong_nth_total_default by (metis (no_types))

context
  fixes d
begin

primrec nth_total'  :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "nth_total' [] n = d" |
  "nth_total' (x # xs) n = (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> nth_total' xs k)"

lemma measurable_nth_total':
  assumes d: "d \<in> space M"
  shows "(\<lambda> (n,xs). nth_total' xs n) \<in> (count_space UNIV) \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M M"
  unfolding nth_total'_def using assms
  by(intro  measurable_rec_list''_func, auto simp add: d)

lemma nth_total_nth_total':
  shows "nth_total d xs n = nth_total' xs n"
proof(induction xs arbitrary: n)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  thus ?case unfolding nth_total'.simps nth_total.simps
    by meson
qed

end (*end of context*)

lemma measurable_nth_total[measurable]:
  assumes "d \<in> space M"
  shows "(\<lambda> (n,xs). nth_total d xs n) \<in> (count_space UNIV) \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M M"
  by (auto simp: measurable_nth_total'[OF assms] nth_total_nth_total')

subsubsection \<open> Definition and Measurability of list insert. \<close>

definition list_insert  :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_insert x xs i = (take i xs) @ [x] @ (drop i xs)"

value"list_insert (15 :: nat) [] (0 :: nat)  :: nat list"
value"list_insert (15 :: nat) [] (1 :: nat)  :: nat list"
value"list_insert (15 :: nat) [1,2,3] (0 :: nat) :: nat list"
value"list_insert (15 :: nat) [1,2,3] (1 :: nat)  :: nat list"
value"list_insert (15 :: nat) [1,2,3] (2 :: nat) :: nat list"
value"list_insert (15 :: nat) [1,2,3] (3 :: nat) :: nat list"
value"list_insert (15 :: nat) [1,2,3] (4 :: nat) :: nat list"

lemma measurable_list_insert[measurable]:
  fixes n :: nat
  shows "(\<lambda> (d,xs). list_insert d xs n) \<in> M \<Otimes>\<^sub>M listM M \<rightarrow>\<^sub>M listM M"
  unfolding list_insert_def by measurable

primrec list_insert'  :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_insert' d [] n = [d]"
| "list_insert' d (x # xs) n = (case n of 0 \<Rightarrow> d # (x # xs) | Suc k \<Rightarrow> x # (list_insert' d xs k))"

lemma list_insert'_is_list_insert:
  shows "list_insert' x xs i = list_insert x xs i"
proof(induction xs arbitrary: x i)
  case Nil
  thus ?case unfolding list_insert_def by auto
next
  case (Cons a xs)
  thus ?case
  proof(cases"i = 0")
    case True
    thus ?thesis unfolding list_insert_def list_insert'.simps(2) take.simps(2) drop.simps(2) by auto
  next
    case False
    then obtain j :: nat where i: "i = Suc j"
      using not0_implies_Suc by auto
    thus ?thesis unfolding i list_insert_def list_insert'.simps(2) take.simps(2) drop.simps(2) using Cons
      using list_insert_def by fastforce
  qed
qed


definition list_exclude :: "nat\<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_exclude n xs = ((take n xs) @ (drop (Suc n) xs))"

value"list_exclude (0 :: nat) [] :: nat list"
value"list_exclude (0 :: nat) [1,2] :: nat list"
value"list_exclude (1 :: nat) [1,2] :: nat list"
value"list_exclude (2 :: nat) [1,2] :: nat list"

lemma measurable_list_exclude[measurable]:
  shows "list_exclude n \<in> listM M \<rightarrow>\<^sub>M listM M"
  unfolding list_exclude_def by measurable

lemma insert_exclude:
  shows "n < length xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> list_insert' (nth_total d xs n) (list_exclude n xs) n = xs"
  unfolding list_exclude_def
proof(induction xs arbitrary : d n)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  thus "n < length (a # xs) \<Longrightarrow> a # xs \<noteq> [] \<Longrightarrow> list_insert' (nth_total d (a # xs) n) (take n (a # xs) @ drop (Suc n) (a # xs)) n = a # xs"
  proof(cases"xs = []")
    case True
    then have q: "a # xs = [a]" and "n = 0"
      using Cons by auto
    thus ?thesis
      by auto
  next
    case False
    thus "n < length (a # xs) \<Longrightarrow> list_insert' (nth_total d (a # xs) n) (take n (a # xs) @ drop (Suc n) (a # xs)) n = a # xs"
    proof(induction n)
      case 0
      then obtain b ys where xs: "xs = b # ys"
        using list_to_pair.cases by auto
      thus ?case
        by auto
    next
      case (Suc n)
      have  "n < length xs"
        using Suc by auto
      thus ?case
        using False Cons(1) by auto
    qed
  qed
qed

subsubsection \<open> Measurability of @{term list_update}\<close>

lemma update_insert_exclude:
  shows "n < length xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> list_update xs n x = list_insert' x (list_exclude n xs) n"
proof(induction xs arbitrary : x n)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  thus "n < length (a # xs) \<Longrightarrow>(a # xs) \<noteq> [] \<Longrightarrow> list_update (a # xs) n x = list_insert' x (list_exclude n (a # xs)) n"
  proof(cases"xs = []")
    case True
    with Cons have q: "a # xs = [a]" and q2: "n = 0"by auto
    show ?thesis unfolding q q2 list_exclude_def by auto
  next
    case False
    thus "n < length (a # xs) \<Longrightarrow>(a # xs) \<noteq> [] \<Longrightarrow> list_update (a # xs) n x = list_insert' x (list_exclude n (a # xs)) n"
    proof(induction n)
      case 0
      then obtain b ys where xs: "xs = b # ys"
        using list_to_pair.cases by auto
      show ?case unfolding xs list_exclude_def by auto
    next
      case (Suc n)
      have nn: "n < length xs"using Suc by auto
      thus ?case unfolding list_exclude_def list_insert'.simps(2) take.simps(2) drop.simps(2) list_update.simps(2)
        using Cons(1)
        by (metis Cons_eq_appendI False list_exclude_def list_insert'.simps(2) old.nat.simps(5))
    qed
  qed
qed

lemma list_update_def2:
  shows "list_update xs n x = If (n < length xs \<and> xs \<noteq> []) (list_insert' x (list_exclude n xs) n) xs"
proof(cases"(n < length xs \<and> xs \<noteq> [])")
  case True
  thus ?thesis by(subst update_insert_exclude,auto)
next
  case False
  thus ?thesis by auto
qed

lemma measurable_list_update[measurable]:
  shows "(\<lambda> (x,xs). list_update xs (n :: nat) x) \<in> M \<Otimes>\<^sub>M (listM M) \<rightarrow>\<^sub>M (listM M)"
proof-
  have 1 : "(\<lambda>x. length (snd x)) \<in>  (M \<Otimes>\<^sub>M listM M) \<rightarrow>\<^sub>M (count_space UNIV)"
    by auto
  have "(\<lambda>x. snd x \<noteq> []) = (\<lambda>xs. (length xs \<noteq> 0)) o snd"
    by auto
  also have "... \<in> (M \<Otimes>\<^sub>M listM M) \<rightarrow>\<^sub>M (count_space (UNIV :: bool set))"
    by measurable
  finally have "Measurable.pred (M \<Otimes>\<^sub>M listM M) (\<lambda>x. snd x \<noteq> [])".
  thus ?thesis
    unfolding  list_insert'_is_list_insert list_update_def2
    using 1 by auto
qed

subsubsection \<open> Measurability of @{term zip}\<close>

lemma measurable_zip[measurable]:
  shows "(\<lambda>(xs,ys). (zip xs ys)) \<in> (listM M) \<Otimes>\<^sub>M (listM N) \<rightarrow>\<^sub>M (listM (M \<Otimes>\<^sub>M N))"
  unfolding zip_def
  by(rule measurable_rec_list''_func,auto)

subsubsection \<open> Measurability of @{term map2}\<close>

lemma measurable_map2[measurable]:
  assumes [measurable]: "(\<lambda>(x,y). f x y) \<in> M \<Otimes>\<^sub>M M' \<rightarrow>\<^sub>M N "
  shows "(\<lambda>(xs,ys). map2 f xs ys) \<in> (listM M) \<Otimes>\<^sub>M (listM M') \<rightarrow>\<^sub>M (listM N)"
  by auto

end