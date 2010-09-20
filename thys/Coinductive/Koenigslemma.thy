(*  Title:       Koenig's lemma with paths modelled as coinductive lists
    Author:      Andreas Lochbihler
*)

header {* Example: Koenig's lemma *}

theory Koenigslemma imports 
  Coinductive_List_Lib 
  Infinite_Set
begin

types 'node graph = "'node \<Rightarrow> 'node \<Rightarrow> bool"
types 'node path = "'node llist"

coinductive_set paths :: "'node graph \<Rightarrow> 'node path set"
for graph :: "'node graph"
where
  Empty: "LNil \<in> paths graph"
| Single: "LCons x LNil \<in> paths graph"
| LCons: "\<lbrakk> graph x y; LCons y xs \<in> paths graph \<rbrakk> \<Longrightarrow> LCons x (LCons y xs) \<in> paths graph"

definition connected :: "'node graph \<Rightarrow> bool"
where "connected graph \<longleftrightarrow> (\<forall>n n'. \<exists>xs. llist_of (n # xs @ [n']) \<in> paths graph)"

inductive_set reachable_via :: "'node graph \<Rightarrow> 'node set \<Rightarrow> 'node \<Rightarrow> 'node set"
for graph :: "'node graph" and ns :: "'node set" and n :: "'node"
where "\<lbrakk> LCons n xs \<in> paths graph; n' \<in> lset xs; lset xs \<subseteq> ns \<rbrakk> \<Longrightarrow> n' \<in> reachable_via graph ns n"


lemma connectedD: "connected graph \<Longrightarrow> \<exists>xs. llist_of (n # xs @ [n']) \<in> paths graph"
unfolding connected_def by blast

lemma paths_LConsD: 
  assumes "LCons x xs \<in> paths graph"
  shows "xs \<in> paths graph"
using assms
by(coinduct)(fastsimp elim: paths.cases del: disjCI)

lemma paths_lappendD1:
  assumes "lappend xs ys \<in> paths graph"
  shows "xs \<in> paths graph"
using assms
apply coinduct
apply(erule paths.cases)
  apply simp
 apply(case_tac x)
  apply simp
 apply simp
apply(case_tac x)
 apply simp
apply(case_tac l')
 apply simp
apply simp
done

lemma paths_lappendD2:
  assumes "lfinite xs"
  and "lappend xs ys \<in> paths graph"
  shows "ys \<in> paths graph"
using assms
by induct(fastsimp elim: paths.cases intro: paths.intros)+

lemma path_avoid_node:
  assumes path: "LCons n xs \<in> paths graph"
  and set: "x \<in> lset xs"
  and n_neq_x: "n \<noteq> x"
  shows "\<exists>xs'. LCons n xs' \<in> paths graph \<and> lset xs' \<subseteq> lset xs \<and> x \<in> lset xs' \<and> n \<notin> lset xs'"
proof -
  from set obtain xs' xs'' where "lfinite xs'" 
    and xs: "xs = lappend xs' (LCons x xs'')" 
    and "x \<notin> lset xs'"
    by(blast dest: split_llist_first)
  show ?thesis
  proof(cases "n \<in> lset xs'")
    case False
    let ?xs' = "lappend xs' (LCons x LNil)"
    from xs path have "lappend (LCons n (lappend xs' (LCons x LNil))) xs'' \<in> paths graph"
      by(simp add: lappend_assoc)
    hence "LCons n ?xs' \<in> paths graph" by(rule paths_lappendD1)
    moreover have "x \<in> lset ?xs'" "lset ?xs' \<subseteq> lset xs" "n \<notin> lset ?xs'"
      using xs False `lfinite xs'` n_neq_x by auto
    ultimately show ?thesis by blast
  next
    case True
    from `lfinite xs'` obtain XS' where xs': "xs' = llist_of XS'"
      unfolding lfinite_eq_range_llist_of by blast
    with True have "n \<in> set XS'" by simp
    from split_list_last[OF this]
    obtain ys zs where XS': "XS' = ys @ n # zs"
      and "n \<notin> set zs" by blast
    let ?xs' = "lappend (llist_of zs) (LCons x LNil)"
    have "lfinite (LCons n (llist_of ys))" by simp
    moreover from xs xs' XS' path
    have "lappend (LCons n (llist_of ys)) (lappend (LCons n ?xs') xs'') \<in> paths graph"
      by(simp add: lappend_assoc)(metis lappend_assoc lappend_llist_of_LCons lappend_llist_of_llist_of llist_of.simps(2))
    ultimately have "lappend (LCons n ?xs') xs'' \<in> paths graph"
      by(rule paths_lappendD2)
    hence "LCons n ?xs' \<in> paths graph" by(rule paths_lappendD1)
    moreover have "x \<in> lset ?xs'" "lset ?xs' \<subseteq> lset xs" "n \<notin> lset ?xs'"
      using xs xs' XS' `lfinite xs'` n_neq_x `n \<notin> set zs` by auto
    ultimately show ?thesis by blast
  qed
qed

lemma reachable_via_subset_unfold:
  "reachable_via graph ns n \<subseteq> (\<Union>n' \<in> {n'. graph n n'} \<inter> ns. insert n' (reachable_via graph (ns - {n'}) n'))"
  (is "?lhs \<subseteq> ?rhs")
proof(rule subsetI)
  fix x
  assume "x \<in> ?lhs"
  then obtain xs where path: "LCons n xs \<in> paths graph"
    and "x \<in> lset xs" "lset xs \<subseteq> ns" by cases

  from `x \<in> lset xs` obtain n' xs' where xs: "xs = LCons n' xs'" by(cases xs) auto
  with path have "graph n n'" by cases simp_all
  moreover from `lset xs \<subseteq> ns` xs have "n' \<in> ns" by simp
  ultimately have "n' \<in> {n'. graph n n'} \<inter> ns" by simp
  thus "x \<in> ?rhs"
  proof(rule UN_I)
    show "x \<in> insert n' (reachable_via graph (ns - {n'}) n')"
    proof(cases "x = n'")
      case True thus ?thesis by simp
    next
      case False
      with xs `x \<in> lset xs` have "x \<in> lset xs'" by simp
      with path xs have path': "LCons n' xs' \<in> paths graph" by cases simp_all
      from `lset xs \<subseteq> ns` xs have "lset xs' \<subseteq> ns" by simp
      
      from path_avoid_node[OF path' `x \<in> lset xs'`] False
      obtain xs'' where path'': "LCons n' xs'' \<in> paths graph"
        and "lset xs'' \<subseteq> lset xs'" "x \<in> lset xs''" "n' \<notin> lset xs''" by blast
      with False `lset xs \<subseteq> ns` xs show ?thesis by(auto intro: reachable_via.intros)
    qed
  qed
qed

theorem koenigslemma:
  fixes graph :: "'node graph"
  and n :: 'node
  assumes connected: "connected graph"
  and infinite: "infinite (UNIV :: 'node set)"
  and finite_branching: "\<And>n. finite {n'. graph n n'}"
  shows "\<exists>xs \<in> paths graph. n \<in> lset xs \<and> \<not> lfinite xs \<and> ldistinct xs"
proof(intro bexI conjI)
  let ?P = "\<lambda>(n, ns) n'. graph n n' \<and> infinite (reachable_via graph (- insert n (insert n' ns)) n') \<and> n' \<notin> insert n ns"
  def xs' == "\<lambda>(n, ns). Some (n, let n' = SOME n'. ?P (n, ns) n' in (n', insert n ns))"
  def xs == "llist_corec (n, {}) xs'"
  let ?X = "\<lambda>xs. \<exists>n ns. xs = llist_corec (n, ns) xs' \<and> finite ns \<and> infinite (reachable_via graph (- insert n ns) n)"

  have [simp]: "\<And>n ns. xs' (n, ns) = Some (n, let n' = SOME n'. ?P (n, ns) n' in (n', insert n ns))"
    unfolding xs'_def by simp

  { fix n ns
    assume "infinite (reachable_via graph (- insert n ns) n)"
    hence "\<exists>n'. ?P (n, ns) n'"
    proof(rule contrapos_np)
      assume "\<not> ?thesis"
      hence fin: "\<And>n'. \<lbrakk> graph n n'; n' \<notin> insert n ns \<rbrakk> \<Longrightarrow> finite (reachable_via graph (- insert n (insert n' ns)) n')"
        by blast
        
      from reachable_via_subset_unfold[of graph "- insert n ns" n]
      show "finite (reachable_via graph (- insert n ns) n)"
      proof(rule finite_subset[OF _ finite_UN_I])
        from finite_branching[of n]
        show "finite ({n'. graph n n'} \<inter> - insert n ns)" by blast
      next
        fix n'
        assume "n' \<in> {n'. graph n n'} \<inter> - insert n ns"
        hence "graph n n'" "n' \<notin> insert n ns" by simp_all
        from fin[OF this] have "finite (reachable_via graph (- insert n (insert n' ns)) n')" .
        moreover have "- insert n (insert n' ns) = - insert n ns - {n'}" by auto
        ultimately show "finite (insert n' (reachable_via graph (- insert n ns - {n'}) n'))" by simp
      qed
    qed }
  note ex_P_I = this

  { fix n :: 'node and ns :: "'node set" and x :: 'node
    assume "x \<in> lset (llist_corec (n, ns) xs')" "n \<notin> ns"
      and "finite ns" "infinite (reachable_via graph (- insert n ns) n)"
    hence "x \<notin> ns"
    proof(induct "llist_corec (n, ns) xs'" arbitrary: n ns)
      case (find xs)
      thus ?case by(subst (asm) llist_corec) simp
    next
      case (step x' xs)
      let ?n' = "Eps (?P (n, ns))" 
        and ?ns' = "insert n ns"
      from `LCons x' xs = llist_corec (n, ns) xs'`
      obtain [simp]: "x' = n" and xs: "xs = llist_corec (?n', ?ns') xs'"
        by(subst (asm) llist_corec) simp
      from `infinite (reachable_via graph (- insert n ns) n)`
      have "\<exists>n'. ?P (n, ns) n'" by(rule ex_P_I)
      hence P: "?P (n, ns) ?n'" by(rule someI_ex)
      moreover have "insert ?n' ?ns' = insert n (insert ?n' ns)" by auto
      ultimately have "?n' \<notin> ?ns'" "finite ?ns'" 
        and "infinite (reachable_via graph (- insert ?n' ?ns') ?n')"
        using `finite ns` by auto
      with xs have "x \<notin> ?ns'" by(rule step)
      thus ?case by simp
    qed }
  note lset = this

  show "n \<in> lset xs" unfolding xs_def xs'_def by(subst llist_corec) simp

  { fix n ns
    assume "lfinite (llist_corec (n, ns) xs')"
    hence False
    proof(induct "llist_corec (n, ns) xs'" arbitrary: n ns)
      case lfinite_LNil thus ?case by(subst (asm) llist_corec)(clarsimp)
    next
      case lfinite_LConsI thus ?case 
        by(subst (asm) (2) llist_corec)(auto simp add: Let_def xs'_def split_beta)
    qed }
  from this[of n "{}"] show "\<not> lfinite xs" by(auto simp add: xs_def)

  have "reachable_via graph (- {n}) n \<supseteq> - {n}"
  proof(rule subsetI)
    fix n' :: 'node
    assume "n' \<in> - {n}"
    hence "n \<noteq> n'" by auto
    from connected obtain xs
      where "llist_of (n # xs @ [n']) \<in> paths graph"
      by(blast dest: connectedD)
    hence "LCons n (llist_of (xs @ [n'])) \<in> paths graph"
      and "n' \<in> lset (llist_of (xs @ [n']))" by simp_all
    from path_avoid_node[OF this `n \<noteq> n'`] show "n' \<in> reachable_via graph (- {n}) n"
      by(auto intro: reachable_via.intros)
  qed
  hence "infinite (reachable_via graph (- {n}) n)"
    using infinite by(auto dest: finite_subset)
  hence X: "?X xs" unfolding xs_def by(auto)

  thus "xs \<in> paths graph"
  proof(coinduct)
    case (paths xs)
    then obtain n ns where xs_def: "xs = llist_corec (n, ns) xs'"
      and "finite ns" and "infinite (reachable_via graph (- insert n ns) n)" by blast
    from `infinite (reachable_via graph (- insert n ns) n)`
    have "\<exists>n'. ?P (n, ns) n'" by(rule ex_P_I)
    hence P: "?P (n, ns) (Eps (?P (n, ns)))" by(rule someI_ex)
    let ?n' = "Eps (?P (n, ns))"
    let ?ns' = "insert n ns"
    let ?n'' = "Eps (?P (?n', ?ns'))"
    let ?ns'' = "insert ?n' ?ns'"
    have "xs = LCons n (LCons ?n' (llist_corec (?n'', ?ns'') xs'))"
      unfolding xs_def by(subst llist_corec)(subst llist_corec, simp add: Let_def)
    moreover from P have "graph n ?n'" by simp
    moreover {
      have "LCons ?n' (llist_corec (?n'', ?ns'') xs') = llist_corec (?n', ?ns') xs'"
        by(subst (2) llist_corec)(simp add: Let_def)
      moreover have "finite ?ns'" using `finite ns` by simp
      moreover have "insert ?n' ?ns' = insert n (insert ?n' ns)" by auto
      hence "infinite (reachable_via graph (- insert ?n' ?ns') ?n')" using P by simp
      ultimately have "?X (LCons ?n' (llist_corec (?n'', ?ns'') xs'))" by blast }
    ultimately have ?LCons by simp
    thus ?case by simp
  qed
  
  from X show "ldistinct xs"
  proof(coinduct)
    case (ldistinct xs)
    then obtain n ns where xs_def: "xs = llist_corec (n, ns) xs'"
      and "finite ns"
      and "infinite (reachable_via graph (- insert n ns) n)" by blast
    from `infinite (reachable_via graph (- insert n ns) n)`
    have "\<exists>n'. ?P (n, ns) n'" by(rule ex_P_I)
    hence P: "?P (n, ns) (Eps (?P (n, ns)))" by(rule someI_ex)
    let ?n' = "Eps (?P (n, ns))"
    let ?ns' = "insert n ns"
    have "xs = LCons n (llist_corec (?n', ?ns') xs')"
      unfolding xs_def by(subst llist_corec)(simp add: Let_def)
    moreover have eq: "insert ?n' ?ns' = insert n (insert ?n' ns)" by auto
    hence "n \<notin> lset (llist_corec (?n', ?ns') xs')" 
      using P `finite ns` by(auto dest: lset)
    moreover from `finite ns` P eq
    have "?X (llist_corec (?n', ?ns') xs')" by(fastsimp intro!: exI refl)
    ultimately have ?LCons by simp
    thus ?case by simp
  qed
qed

end